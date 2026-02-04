use crate::leg::LegEncryption;
use crate::{Error, LEG_ENC_LABEL, NONCE_LABEL, add_to_transcript, error};
use ark_ec::AffineRepr;
use ark_ec::CurveGroup;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::{vec, vec::Vec};
use core::ops::Neg;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::AssetId;
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
        asset_id: AssetId,
        mediator_sk: G::ScalarField,
        accept: bool,
        index_in_asset_data: usize,
        nonce: &[u8],
        enc_gen: G,
    ) -> error::Result<Self> {
        let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);
        Self::new_with_given_transcript(
            rng,
            leg_enc,
            asset_id,
            mediator_sk,
            accept,
            index_in_asset_data,
            nonce,
            enc_gen,
            &mut transcript,
        )
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: LegEncryption<G>,
        asset_id: AssetId,
        mut mediator_sk: G::ScalarField,
        accept: bool,
        index_in_asset_data: usize,
        nonce: &[u8],
        enc_gen: G,
        mut transcript: &mut MerlinTranscript,
    ) -> error::Result<Self> {
        ensure_correct_index(&leg_enc, index_in_asset_data)?;

        // Hash the mediator's response
        if accept {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_ACCEPT_RESPONSE);
        } else {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_REJECT_RESPONSE);
        }

        let D = leg_enc.eph_pk_auds_meds[index_in_asset_data].1.3;
        let minus_h = enc_gen.into_group().neg().into_affine();
        let enc_pk = PokPedersenCommitmentProtocol::init(
            mediator_sk,
            G::ScalarField::rand(rng),
            &leg_enc.ct_asset_id,
            mediator_sk * G::ScalarField::from(asset_id),
            G::ScalarField::rand(rng),
            &minus_h,
        );

        Zeroize::zeroize(&mut mediator_sk);

        enc_pk.challenge_contribution(&leg_enc.ct_asset_id, &minus_h, &D, &mut transcript)?;

        add_to_transcript!(
            transcript,
            LEG_ENC_LABEL,
            leg_enc,
            INDEX_IN_ASSET_DATA_LABEL,
            index_in_asset_data,
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
        index_in_asset_data: usize,
        nonce: &[u8],
        enc_gen: G,
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> error::Result<()> {
        let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);
        self.verify_with_given_transcript(
            leg_enc,
            accept,
            index_in_asset_data,
            nonce,
            enc_gen,
            &mut transcript,
            rmc,
        )
    }

    pub fn verify_with_given_transcript(
        &self,
        leg_enc: LegEncryption<G>,
        accept: bool,
        index_in_asset_data: usize,
        nonce: &[u8],
        enc_gen: G,
        mut transcript: &mut MerlinTranscript,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> error::Result<()> {
        if index_in_asset_data >= leg_enc.eph_pk_auds_meds.len() {
            return Err(Error::InvalidKeyIndex(index_in_asset_data));
        }
        // Role should be false for mediator
        if leg_enc.eph_pk_auds_meds[index_in_asset_data].0 {
            return Err(Error::MediatorNotFoundAtIndex(index_in_asset_data));
        }

        // Hash the mediator's response
        if accept {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_ACCEPT_RESPONSE);
        } else {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_REJECT_RESPONSE);
        }

        let D = leg_enc.eph_pk_auds_meds[index_in_asset_data].1.3;
        let minus_h = enc_gen.into_group().neg().into_affine();

        self.resp_enc_pk.challenge_contribution(
            &leg_enc.ct_asset_id,
            &minus_h,
            &D,
            &mut transcript,
        )?;

        add_to_transcript!(
            transcript,
            LEG_ENC_LABEL,
            leg_enc,
            INDEX_IN_ASSET_DATA_LABEL,
            index_in_asset_data,
            NONCE_LABEL,
            nonce
        );

        let challenge = transcript.challenge_scalar::<G::ScalarField>(MEDIATOR_TXN_CHALLENGE_LABEL);

        match rmc.as_mut() {
            Some(rmc) => {
                self.resp_enc_pk.verify_using_randomized_mult_checker(
                    D,
                    leg_enc.ct_asset_id,
                    minus_h,
                    &challenge,
                    rmc,
                );
            }
            None => {
                if !self
                    .resp_enc_pk
                    .verify(&D, &leg_enc.ct_asset_id, &minus_h, &challenge)
                {
                    return Err(Error::ProofVerificationError(
                        "resp_enc_pk verification failed".into(),
                    ));
                }
            }
        }

        Ok(())
    }
}

fn ensure_correct_index<G: AffineRepr>(
    leg_enc: &LegEncryption<G>,
    index_in_asset_data: usize,
) -> error::Result<()> {
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        if index_in_asset_data >= leg_enc.eph_pk_auds_meds.len() {
            return Err(Error::InvalidKeyIndex(index_in_asset_data));
        }
        // Role should be false for mediator
        if leg_enc.eph_pk_auds_meds[index_in_asset_data].0 {
            return Err(Error::MediatorNotFoundAtIndex(index_in_asset_data));
        }
        Ok(())
    }
}
