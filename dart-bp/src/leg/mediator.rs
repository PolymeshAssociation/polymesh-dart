use crate::leg::LegEncryption;
use crate::{Error, LEG_ENC_LABEL, NONCE_LABEL, add_to_transcript, error::Result};
use ark_ec::AffineRepr;
use ark_ff::Field;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::vec::Vec;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{PokPedersenCommitment, PokPedersenCommitmentProtocol};
use zeroize::Zeroize;

pub const INDEX_IN_ASSET_DATA_LABEL: &'static [u8; 19] = b"index_in_asset_data";
pub const MEDIATOR_TXN_LABEL: &[u8; 12] = b"mediator-txn";
pub const MEDIATOR_TXN_RESPONSE_LABEL: &[u8; 17] = b"mediator-response";
pub const MEDIATOR_TXN_ACCEPT_RESPONSE: &[u8; 6] = b"accept";
pub const MEDIATOR_TXN_REJECT_RESPONSE: &[u8; 6] = b"reject";
pub const MEDIATOR_TXN_CHALLENGE_LABEL: &[u8; 22] = b"mediator-txn-challenge";
pub const MEDIATOR_TXN_INSTANCE_LABEL: &[u8; 27] = b"mediator-txn-extra-instance";

/// This is the proof for mediator affirm/reject. Report section 5.1.12
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MediatorTxnProof<G: AffineRepr> {
    pub resp_enc_pk: PokPedersenCommitment<G>,
}

impl<G: AffineRepr> MediatorTxnProof<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: LegEncryption<G>,
        enc_sk: G::ScalarField,
        mediator_sk: G::ScalarField,
        accept: bool,
        is_public_mediator: bool,
        index: usize,
        nonce: &[u8],
        sig_key_gen: &G,
    ) -> Result<Self> {
        let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);
        Self::new_with_given_transcript(
            rng,
            leg_enc,
            enc_sk,
            mediator_sk,
            accept,
            is_public_mediator,
            index,
            nonce,
            sig_key_gen,
            &mut transcript,
        )
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: LegEncryption<G>,
        enc_sk: G::ScalarField,
        mut mediator_sk: G::ScalarField,
        accept: bool,
        is_public_mediator: bool,
        index: usize,
        nonce: &[u8],
        sig_key_gen: &G,
        mut transcript: &mut MerlinTranscript,
    ) -> Result<Self> {
        ensure_correct_index(&leg_enc, is_public_mediator, index)?;

        // Hash the mediator's response
        if accept {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_ACCEPT_RESPONSE);
        } else {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_REJECT_RESPONSE);
        }

        let y = if is_public_mediator {
            &leg_enc.ct_public_meds[index]
        } else {
            &leg_enc.ct_meds[index]
        };
        let eph_pk = if is_public_mediator {
            &leg_enc.eph_pk_public_med_keys[index].1
        } else {
            &leg_enc.eph_pk_med_keys[index].1
        };
        let enc_pk = PokPedersenCommitmentProtocol::init(
            enc_sk.inverse().ok_or(Error::InvertingZero)?,
            G::ScalarField::rand(rng),
            eph_pk,
            mediator_sk,
            G::ScalarField::rand(rng),
            sig_key_gen,
        );

        Zeroize::zeroize(&mut mediator_sk);

        enc_pk.challenge_contribution(eph_pk, sig_key_gen, &y, &mut transcript)?;

        add_to_transcript!(
            transcript,
            LEG_ENC_LABEL,
            leg_enc,
            INDEX_IN_ASSET_DATA_LABEL,
            index,
            NONCE_LABEL,
            nonce
        );

        let challenge = transcript.challenge_scalar::<G::ScalarField>(MEDIATOR_TXN_CHALLENGE_LABEL);

        let resp_enc_pk = enc_pk.gen_proof(&challenge);
        Ok(Self { resp_enc_pk })
    }

    pub fn verify(
        &self,
        leg_enc: LegEncryption<G>,
        accept: bool,
        is_public_mediator: bool,
        index: usize,
        nonce: &[u8],
        sig_key_gen: G,
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);
        self.verify_with_given_transcript(
            leg_enc,
            accept,
            is_public_mediator,
            index,
            nonce,
            sig_key_gen,
            &mut transcript,
            rmc,
        )
    }

    pub fn verify_with_given_transcript(
        &self,
        leg_enc: LegEncryption<G>,
        accept: bool,
        is_public_mediator: bool,
        index: usize,
        nonce: &[u8],
        sig_key_gen: G,
        mut transcript: &mut MerlinTranscript,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        if is_public_mediator {
            if leg_enc.ct_public_meds.len() != leg_enc.eph_pk_public_med_keys.len() {
                return Err(Error::ProofVerificationError(
                    "ct_public_meds and eph_pk_public_med_keys length mismatch".to_string(),
                ));
            }
            if index >= leg_enc.ct_public_meds.len() {
                return Err(Error::InvalidKeyIndex(index));
            }
        } else {
            if leg_enc.ct_meds.len() != leg_enc.eph_pk_med_keys.len() {
                return Err(Error::ProofVerificationError(
                    "ct_meds and eph_pk_med_keys length mismatch".to_string(),
                ));
            }
            if index >= leg_enc.ct_meds.len() {
                return Err(Error::InvalidKeyIndex(index));
            }
        }

        // Hash the mediator's response
        if accept {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_ACCEPT_RESPONSE);
        } else {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_REJECT_RESPONSE);
        }

        let y = if is_public_mediator {
            leg_enc.ct_public_meds[index]
        } else {
            leg_enc.ct_meds[index]
        };
        let eph_pk = if is_public_mediator {
            leg_enc.eph_pk_public_med_keys[index].1
        } else {
            leg_enc.eph_pk_med_keys[index].1
        };

        self.resp_enc_pk
            .challenge_contribution(&eph_pk, &sig_key_gen, &y, &mut transcript)?;

        add_to_transcript!(
            transcript,
            LEG_ENC_LABEL,
            leg_enc,
            INDEX_IN_ASSET_DATA_LABEL,
            index,
            NONCE_LABEL,
            nonce
        );

        let challenge = transcript.challenge_scalar::<G::ScalarField>(MEDIATOR_TXN_CHALLENGE_LABEL);

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

fn ensure_correct_index<G: AffineRepr>(
    leg_enc: &LegEncryption<G>,
    is_public_mediator: bool,
    index: usize,
) -> Result<()> {
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        if is_public_mediator {
            if index >= leg_enc.ct_public_meds.len() {
                return Err(Error::InvalidKeyIndex(index));
            }
        } else {
            if index >= leg_enc.ct_meds.len() {
                return Err(Error::InvalidKeyIndex(index));
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keys::keygen_enc;
    use crate::leg::{Leg, LegEncConfig};
    use ark_ec::CurveGroup;
    use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
    use std::time::Instant;

    #[test]
    fn mediator_action() {
        let mut rng = rand::thread_rng();

        let label = b"testing";
        let sig_key_gen = hash_to_pallas(label, b"sk-gen").into_affine();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        // Encryption keys
        let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let num_auditors = 2;
        let num_mediators = 3;
        let keys_auditor = (0..num_auditors)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_enc(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();

        let mut keys = Vec::with_capacity(num_auditors + num_mediators);
        keys.extend(
            keys_auditor
                .iter()
                .map(|(s, k)| (true, k.0, s.0))
                .into_iter(),
        );
        keys.extend(
            keys_mediator
                .iter()
                .map(|(s, k)| (false, k.0, s.0))
                .into_iter(),
        );

        // Indices of encryption keys corresponding to each mediator. There could be other ways of assigning encryption keys to mediators
        // and the best is to have just one encryption key shared among all but doing this just for testing
        let mediator_enc_key_indices = (0..num_mediators)
            .map(|i| {
                if i < num_auditors {
                    i as u8
                } else {
                    (num_auditors - 1) as u8
                }
            })
            .collect::<Vec<_>>();

        let leg = Leg::new(
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            keys_auditor.iter().map(|(_, k)| k.0).collect(),
            keys_mediator
                .iter()
                .enumerate()
                .map(|(i, (_, k))| (mediator_enc_key_indices[i], k.0))
                .collect(),
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc, _) = leg
            .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
            .unwrap();

        // Venue has successfully created the leg and its commitment has been stored on chain

        let nonce = b"test-nonce";

        // Mediator "accept"ing in this case
        let accept = true;

        for mediator_index in 0..num_mediators {
            let clock = Instant::now();
            let proof = MediatorTxnProof::new(
                &mut rng,
                leg_enc.clone(),
                keys_auditor[mediator_enc_key_indices[mediator_index] as usize]
                    .0
                    .0,
                keys_mediator[mediator_index].0.0,
                accept,
                false,
                mediator_index,
                nonce,
                &sig_key_gen,
            )
            .unwrap();
            let prover_time = clock.elapsed();

            let clock = Instant::now();

            proof
                .verify(
                    leg_enc.clone(),
                    accept,
                    false,
                    mediator_index,
                    nonce,
                    sig_key_gen,
                    None,
                )
                .unwrap();

            let verifier_time_regular = clock.elapsed();

            // Test verification with RMC as well
            let clock = Instant::now();
            let mut rmc = RandomizedMultChecker::new(ark_pallas::Fr::rand(&mut rng));
            proof
                .verify(
                    leg_enc.clone(),
                    accept,
                    false,
                    mediator_index,
                    nonce,
                    sig_key_gen,
                    Some(&mut rmc),
                )
                .unwrap();

            assert!(rmc.verify());
            let verifier_time_rmc = clock.elapsed();

            log::info!("proof size = {}", proof.compressed_size());
            log::info!("prover time = {:?}", prover_time);
            log::info!(
                "verifier time (regular) = {:?}, verifier time (RandomizedMultChecker) = {:?}",
                verifier_time_regular,
                verifier_time_rmc
            );

            match proof
                .verify(leg_enc.clone(), accept, false, 10, nonce, sig_key_gen, None)
                .err()
                .unwrap()
            {
                Error::InvalidKeyIndex(i) => assert_eq!(i, 10),
                _ => panic!("Didn't error but should have"),
            }
        }
    }

    #[test]
    fn mediator_verifier_rejects_mismatched_mediator_vectors() {
        let mut rng = rand::thread_rng();

        let label = b"testing";
        let sig_key_gen = hash_to_pallas(label, b"sk-gen").into_affine();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        // Encryption keys
        let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        // One auditor encryption key, one mediator affirmation key.
        let (sk_aud_enc, pk_aud_enc) = keygen_enc(&mut rng, enc_key_gen);
        let (sk_med, pk_med) = keygen_enc(&mut rng, sig_key_gen);

        let leg = Leg::new(
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            vec![pk_aud_enc.0],
            vec![(0u8, pk_med.0)],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc, _) = leg
            .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
            .unwrap();

        let nonce = b"test-nonce";
        let accept = true;
        let index = 0usize;

        let proof = MediatorTxnProof::new(
            &mut rng,
            leg_enc.clone(),
            sk_aud_enc.0,
            sk_med.0,
            accept,
            false,
            index,
            nonce,
            &sig_key_gen,
        )
        .unwrap();

        let mut malformed = leg_enc.clone();
        malformed.eph_pk_med_keys.pop();

        assert!(
            proof
                .verify(malformed, accept, false, index, nonce, sig_key_gen, None)
                .is_err()
        );
    }

    #[test]
    fn mediator_verifier_rejects_mismatched_public_mediator_vectors() {
        let mut rng = rand::thread_rng();

        let label = b"testing";
        let sig_key_gen = hash_to_pallas(label, b"sk-gen").into_affine();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        // Encryption keys
        let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        // One public encryption key and one public mediator affirmation key.
        let (sk_pub_enc, pk_pub_enc) = keygen_enc(&mut rng, enc_key_gen);
        let (sk_med, pk_med) = keygen_enc(&mut rng, sig_key_gen);

        let leg = Leg::new(
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            vec![],
            vec![],
            vec![pk_pub_enc.0],
            vec![(0u8, pk_med.0)],
        )
        .unwrap();
        let (leg_enc, _) = leg
            .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
            .unwrap();

        let nonce = b"test-nonce";
        let accept = true;
        let index = 0usize;

        let proof = MediatorTxnProof::new(
            &mut rng,
            leg_enc.clone(),
            sk_pub_enc.0,
            sk_med.0,
            accept,
            true,
            index,
            nonce,
            &sig_key_gen,
        )
        .unwrap();

        let mut malformed = leg_enc.clone();
        malformed.eph_pk_public_med_keys.pop();

        assert!(
            proof
                .verify(malformed, accept, true, index, nonce, sig_key_gen, None)
                .is_err()
        );
    }
}
