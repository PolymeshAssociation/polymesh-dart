use crate::account::{LegProverConfig, LegVerifierConfig};
use crate::auth_proofs::helpers::{init_acc_comm_protocol, verify_acc_comm};
use crate::auth_proofs::{AUTH_TXN_LABEL, NULLIFIER_LABEL, helpers};
use crate::{
    ACCOUNT_COMMITMENT_LABEL, Error, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL, TXN_CHALLENGE_LABEL,
    add_to_transcript, error,
};
use ark_ec::AffineRepr;
use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::string::ToString;
use ark_std::{UniformRand, format, vec, vec::Vec};
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use schnorr_pok::SchnorrResponse;
use schnorr_pok::discrete_log::{
    PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use schnorr_pok::partial::{
    Partial2PokPedersenCommitment, PartialPokDiscreteLog, PartialPokPedersenCommitment,
    PartialSchnorrResponse,
};

// Auth proof will prove a different relation for ct_amount and ct_asset_id.
// ct_amount_1 = S[2] * sk_enc^{-1} + B * k_1
// ct_asset_id_1 = S[3] * sk_enc^{-1} + B * k_2
//
// Assuming sender above, for receiver use R[2], R[3] instead. S and R are ephemeral public keys for sender and receiver.
//
// Now host will prove
// ct_amount_2 = enc_gen * amount + B * -k_1
// ct_asset_id_2 = enc_gen * asset_id + B * -k_2
//
// Note that ct_amount_1 + ct_amount_2 = ct_amount and ct_asset_id_1 + ct_asset_id_2 = ct_asset_id
//
// Reason is challenge being different for auth proof and host so even if the blindings are same response will be different.

pub const LEG_ENCRYPTION_LABEL: &[u8; 14] = b"leg-encryption";
pub const PARTY_EPH_PK_LABEL: &[u8; 19] = b"party-ephemeral-key";

/// For non-fee account related transactions, affirmation, counter update, reverse
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AuthProofAffirmation<G: AffineRepr> {
    /// The state (commitment) being invalidated through nullifier
    /// For Pedersen commitment to affirmation secret key, encryption secret key and part of randomness used to re-randomize the commitment
    pub t_re_randomized_account_commitment: G,
    pub resp_re_randomized_account_commitment: SchnorrResponse<G>,
    /// The new state (commitment) being created
    /// For Pedersen commitment to affirmation secret key, encryption secret key and a new randomness
    pub t_updated_account_commitment: G,
    pub resp_updated_account_commitment: PartialSchnorrResponse<G>,
    /// `sk_gen * sk + enc_key_gen * sk_enc + comm_re_rand_gen * rand_part_old_comm`
    pub partial_re_randomized_account_commitment: G,
    /// `sk_gen * sk + enc_key_gen * sk_enc + comm_re_rand_gen * rand_1_new_comm`
    pub partial_updated_account_commitment: G,
    /// `ct_amount_1_i = S[2]_i * sk_enc^{-1} + B_blinding * k_1_i`
    pub partial_ct_amounts: Vec<G>,
    /// `ct_asset_id_1_i = S[3] * sk_enc^{-1} + B_blinding * k_2_i`
    pub partial_ct_asset_ids: Vec<G>,
    pub D: G,
    pub resp_enc_key_gen: PokPedersenCommitment<G>,
    pub leg_links: Vec<(
        PartialPokPedersenCommitment<G>,
        Option<Partial2PokPedersenCommitment<G>>,
        RespAssetId<G>,
    )>,
}

impl<G: AffineRepr> AuthProofAffirmation<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        sk: G::ScalarField,
        sk_enc: G::ScalarField,
        rand_part_old_comm: G::ScalarField, // part of commitment randomness used to re-randomize the old state commitment
        rand_new_comm: G::ScalarField, // part of commitment randomness for new state commitment
        // In the order legs appear in legs_with_conf, their length can be smaller than legs_with_conf since some state transitions don't have balance change and/or some reveal asset-id
        k_amounts: Vec<G::ScalarField>,
        k_asset_ids: Vec<G::ScalarField>,
        legs_with_conf: Vec<LegProverConfig<G>>,
        re_randomized_account_commitment: &G,
        updated_account_commitment: &G,
        nullifier: G,
        nonce: &[u8], // This could be the same nonce used by host device or a concatenation of host's nonce and other data like its challenge (if doing sequential)
        sk_gen: G,
        enc_key_gen: G,
        comm_re_rand_gen: G, // generator used blind the old and new commitment parts
        enc_gen: G,
    ) -> error::Result<Self> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);
        Self::new_with_given_transcript(
            rng,
            sk,
            sk_enc,
            rand_part_old_comm,
            rand_new_comm,
            k_amounts,
            k_asset_ids,
            legs_with_conf,
            re_randomized_account_commitment,
            updated_account_commitment,
            nullifier,
            nonce,
            sk_gen,
            enc_key_gen,
            comm_re_rand_gen,
            enc_gen,
            &mut transcript,
        )
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        sk: G::ScalarField,
        sk_enc: G::ScalarField,
        rand_part_old_comm: G::ScalarField, // part of commitment randomness used to re-randomize the old state commitment
        rand_new_comm: G::ScalarField, // part of commitment randomness for new state commitment
        // In the order legs appear in legs_with_conf, their length can be smaller than legs_with_conf since some state transitions don't have balance change and/or some reveal asset-id
        k_amounts: Vec<G::ScalarField>,
        k_asset_ids: Vec<G::ScalarField>,
        legs_with_conf: Vec<LegProverConfig<G>>,
        re_randomized_account_commitment: &G,
        updated_account_commitment: &G,
        nullifier: G,
        nonce: &[u8], // This could be the same nonce used by host device or a concatenation of host's nonce and other data like its challenge (if doing sequential)
        sk_gen: G,
        enc_key_gen: G,
        comm_re_rand_gen: G, // generator used blind the old and new commitment parts
        enc_gen: G,
        mut transcript: &mut MerlinTranscript,
    ) -> error::Result<Self> {
        add_to_transcript!(
            transcript,
            NULLIFIER_LABEL,
            nullifier,
            NONCE_LABEL,
            nonce,
            RE_RANDOMIZED_PATH_LABEL, // TODO: Choose different label or hash the whole path
            re_randomized_account_commitment,
            ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );
        for conf in &legs_with_conf {
            add_to_transcript!(
                transcript,
                LEG_ENCRYPTION_LABEL,
                conf.encryption,
                PARTY_EPH_PK_LABEL,
                conf.party_eph_pk
            );
        }

        let sk_blinding = G::ScalarField::rand(rng);
        let sk_enc_blinding = G::ScalarField::rand(rng);
        let sk_enc_inv_blinding = G::ScalarField::rand(rng);

        let (
            proto_old,
            proto_new,
            partial_re_randomized_account_commitment,
            partial_updated_account_commitment,
        ) = init_acc_comm_protocol(
            rng,
            sk,
            sk_enc,
            rand_part_old_comm,
            rand_new_comm,
            sk_blinding,
            sk_enc_blinding,
            sk_gen,
            enc_key_gen,
            comm_re_rand_gen,
            &mut transcript,
        )?;

        let sk_enc_inv = sk_enc.inverse().ok_or(Error::InvertingZero)?;

        let num_balance_changed = legs_with_conf
            .iter()
            .filter(|c| c.has_balance_changed)
            .count();
        if k_amounts.len() != num_balance_changed {
            return Err(Error::ProofGenerationError(format!(
                "Expected {} k_amounts (one per leg with balance change) but got {}",
                num_balance_changed,
                k_amounts.len()
            )));
        }

        let mut is_asset_id_revealed = false;
        let mut asset_id = None;
        for conf in &legs_with_conf {
            if is_asset_id_revealed {
                if let Some(a) = conf.encryption.asset_id() {
                    if asset_id != Some(a) {
                        return Err(Error::ProofGenerationError(
                            "All legs must have the same asset_id".to_string(),
                        ));
                    }
                }
            } else {
                if let Some(a) = conf.encryption.asset_id() {
                    asset_id = Some(a);
                    is_asset_id_revealed = true;
                }
            }
        }

        let h_at = asset_id.map(|a| enc_gen * G::ScalarField::from(a));

        if !is_asset_id_revealed {
            let expected_k_asset_ids = legs_with_conf
                .iter()
                .filter(|c| !c.encryption.is_asset_id_revealed())
                .count();
            if k_asset_ids.len() != expected_k_asset_ids {
                return Err(Error::ProofGenerationError(format!(
                    "Expected {} k_asset_ids (one per leg with hidden asset_id) but got {}",
                    expected_k_asset_ids,
                    k_asset_ids.len()
                )));
            }
        } else if !k_asset_ids.is_empty() {
            return Err(Error::ProofGenerationError(
                "k_asset_ids must be empty when asset_id is revealed".to_string(),
            ));
        }

        let mut partial_ct_amounts = vec![];
        let mut partial_ct_asset_ids = vec![];
        let mut offset_amount = 0;
        let mut offset_asset_id = 0;

        // let mut legs = Vec::with_capacity(legs_with_conf.len());
        let mut t_leg_link = Vec::with_capacity(legs_with_conf.len());

        enum AssetIdProtocol<G: AffineRepr> {
            RevealedElsewhere(PokDiscreteLogProtocol<G>),
            Hidden(PokPedersenCommitmentProtocol<G>),
            Revealed,
        }

        for conf in legs_with_conf {
            let eph_pk_participant = conf.party_eph_pk.eph_pk_participant();
            let t_participant = PokPedersenCommitmentProtocol::init(
                sk_enc_inv,
                sk_enc_inv_blinding,
                &eph_pk_participant,
                sk_enc,
                sk_enc_blinding,
                &enc_key_gen,
            );
            t_participant.challenge_contribution(
                &eph_pk_participant,
                &enc_key_gen,
                &conf
                    .encryption
                    .ct_participant(conf.party_eph_pk.is_sender()),
                &mut transcript,
            )?;

            let t_amount = if conf.has_balance_changed {
                // If account state transition is changing balance, it would be referring to amount in the leg
                // and thus should prove about it
                assert!(offset_amount < k_amounts.len());
                partial_ct_amounts.push(
                    (comm_re_rand_gen * k_amounts[offset_amount]
                        + conf.party_eph_pk.eph_pk_amount() * sk_enc_inv)
                        .into_affine(),
                );
                let eph_pk_base = conf.party_eph_pk.eph_pk_amount();
                let t_amount = PokPedersenCommitmentProtocol::init(
                    sk_enc_inv,
                    sk_enc_inv_blinding,
                    &eph_pk_base,
                    k_amounts[offset_amount],
                    G::ScalarField::rand(rng),
                    &comm_re_rand_gen,
                );
                t_amount.challenge_contribution(
                    &eph_pk_base,
                    &comm_re_rand_gen,
                    &partial_ct_amounts[offset_amount],
                    &mut transcript,
                )?;

                offset_amount += 1;
                Some(t_amount)
            } else {
                None
            };

            let t_asset_id = if !conf.encryption.is_asset_id_revealed() {
                // If asset id is not revealed in this leg
                let eph_pk_base = conf.party_eph_pk.eph_pk_asset_id().unwrap();
                if is_asset_id_revealed {
                    // If asset id is not revealed in this leg but revealed in some other leg
                    let t_asset_id =
                        PokDiscreteLogProtocol::init(sk_enc_inv, sk_enc_inv_blinding, &eph_pk_base);
                    let y = (conf.encryption.asset_id_ciphertext().unwrap() - h_at.unwrap())
                        .into_affine();
                    t_asset_id.challenge_contribution(&eph_pk_base, &y, &mut transcript)?;
                    AssetIdProtocol::RevealedElsewhere(t_asset_id)
                } else {
                    // If asset id is not revealed in any leg
                    if offset_asset_id >= k_asset_ids.len() {
                        return Err(Error::ProofGenerationError(
                            "Not enough k_asset_ids provided for legs with hidden asset_id"
                                .to_string(),
                        ));
                    }
                    partial_ct_asset_ids.push(
                        (comm_re_rand_gen * k_asset_ids[offset_asset_id]
                            + conf.party_eph_pk.eph_pk_asset_id().unwrap() * sk_enc_inv)
                            .into_affine(),
                    );
                    let t_asset_id = PokPedersenCommitmentProtocol::init(
                        sk_enc_inv,
                        sk_enc_inv_blinding,
                        &eph_pk_base,
                        k_asset_ids[offset_asset_id],
                        G::ScalarField::rand(rng),
                        &comm_re_rand_gen,
                    );
                    t_asset_id.challenge_contribution(
                        &eph_pk_base,
                        &comm_re_rand_gen,
                        &partial_ct_asset_ids[offset_asset_id],
                        &mut transcript,
                    )?;
                    offset_asset_id += 1;
                    AssetIdProtocol::Hidden(t_asset_id)
                }
            } else {
                AssetIdProtocol::Revealed
            };

            t_leg_link.push((t_participant, t_amount, t_asset_id));
        }

        // For proving sk_enc^{-1} relation, create D = enc_key_gen * sk_e + B * r.
        // Now prove D * sk_enc^{-1} - B * r * sk_enc^{-1} = enc_gen
        let r = G::ScalarField::rand(rng);
        let D = (enc_key_gen * sk_enc + comm_re_rand_gen * r).into_affine();
        let t_enc_key_gen = PokPedersenCommitmentProtocol::init(
            sk_enc_inv,
            sk_enc_inv_blinding,
            &D,
            -(r * sk_enc_inv),
            G::ScalarField::rand(rng),
            &comm_re_rand_gen,
        );
        t_enc_key_gen.challenge_contribution(
            &D,
            &comm_re_rand_gen,
            &enc_key_gen,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let (resp_re_randomized_account_commitment, resp_updated_account_commitment) =
            helpers::resp_acc_comm(
                sk,
                sk_enc,
                rand_part_old_comm,
                rand_new_comm,
                &proto_old,
                &proto_new,
                &challenge,
            )?;

        let mut leg_links = Vec::with_capacity(t_leg_link.len());
        for (t_participant, t_amount, t_asset_id) in t_leg_link {
            let resp_participant = t_participant.gen_partial_proof();
            let resp_amount = t_amount.map(|t| t.gen_partial2_proof(&challenge));
            let resp_asset_id = match t_asset_id {
                AssetIdProtocol::Revealed => RespAssetId::Revealed,
                AssetIdProtocol::RevealedElsewhere(p) => {
                    RespAssetId::RevealedElsewhere(p.gen_partial_proof())
                }
                AssetIdProtocol::Hidden(p) => RespAssetId::Hidden(p.gen_partial2_proof(&challenge)),
            };
            leg_links.push((resp_participant, resp_amount, resp_asset_id))
        }

        let resp_enc_key_gen = t_enc_key_gen.gen_proof(&challenge);

        Ok(Self {
            t_re_randomized_account_commitment: proto_old.t,
            resp_re_randomized_account_commitment,
            t_updated_account_commitment: proto_new.t,
            resp_updated_account_commitment,
            partial_re_randomized_account_commitment,
            partial_updated_account_commitment,
            partial_ct_amounts,
            partial_ct_asset_ids,
            D,
            resp_enc_key_gen,
            leg_links,
        })
    }

    pub fn verify(
        &self,
        legs_with_conf: Vec<LegVerifierConfig<G>>,
        re_randomized_account_commitment: &G,
        updated_account_commitment: &G,
        nullifier: G,
        nonce: &[u8],
        sk_gen: G,
        enc_key_gen: G,
        comm_re_rand_gen: G, // generator used blind the old and new commitment parts
        enc_gen: G,
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> error::Result<()> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);
        self.verify_with_given_transcript(
            legs_with_conf,
            re_randomized_account_commitment,
            updated_account_commitment,
            nullifier,
            nonce,
            sk_gen,
            enc_key_gen,
            comm_re_rand_gen,
            enc_gen,
            &mut transcript,
            rmc,
        )
    }

    pub fn verify_with_given_transcript(
        &self,
        legs_with_conf: Vec<LegVerifierConfig<G>>,
        re_randomized_account_commitment: &G,
        updated_account_commitment: &G,
        nullifier: G,
        nonce: &[u8],
        sk_gen: G,
        enc_key_gen: G,
        comm_re_rand_gen: G, // generator used blind the old and new commitment parts
        enc_gen: G,
        mut transcript: &mut MerlinTranscript,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> error::Result<()> {
        add_to_transcript!(
            transcript,
            NULLIFIER_LABEL,
            nullifier,
            NONCE_LABEL,
            nonce,
            RE_RANDOMIZED_PATH_LABEL,
            re_randomized_account_commitment,
            ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        for conf in &legs_with_conf {
            add_to_transcript!(
                transcript,
                LEG_ENCRYPTION_LABEL,
                conf.encryption,
                PARTY_EPH_PK_LABEL,
                conf.party_eph_pk
            );
        }

        self.t_re_randomized_account_commitment
            .serialize_compressed(&mut transcript)?;
        self.partial_re_randomized_account_commitment
            .serialize_compressed(&mut transcript)?;
        self.t_updated_account_commitment
            .serialize_compressed(&mut transcript)?;
        self.partial_updated_account_commitment
            .serialize_compressed(&mut transcript)?;

        if legs_with_conf.len() != self.leg_links.len() {
            return Err(Error::ProofVerificationError(format!(
                "Needed {} leg proofs but got {}",
                legs_with_conf.len(),
                self.leg_links.len()
            )));
        }

        let mut asset_id = None;
        for (i, leg_conf) in legs_with_conf.iter().enumerate() {
            if asset_id.is_none() {
                asset_id = leg_conf.encryption.asset_id();
            } else if leg_conf.encryption.is_asset_id_revealed()
                && (asset_id != leg_conf.encryption.asset_id())
            {
                return Err(Error::ProofVerificationError(format!(
                    "All legs must have the same asset id but mismatch at leg {i}"
                )));
            }
            if leg_conf.has_balance_decreased.is_some() && self.leg_links[i].1.is_none() {
                return Err(Error::ProofVerificationError(format!(
                    "Leg {i} has a balance change but auth proof is missing the amount response"
                )));
            }
            if !leg_conf.encryption.is_asset_id_revealed() {
                if matches!(self.leg_links[i].2, RespAssetId::Revealed) {
                    return Err(Error::ProofVerificationError(format!(
                        "Leg {i} has a hidden asset_id but auth proof marks it as revealed"
                    )));
                }
            }
        }

        let is_asset_id_revealed = asset_id.is_some();

        let h_at = asset_id.map(|a| enc_gen * G::ScalarField::from(a));

        let mut offset_amount = 0;
        let mut offset_asset_id = 0;

        for (i, conf) in legs_with_conf.iter().enumerate() {
            let eph_pk_participant = conf.party_eph_pk.eph_pk_participant();
            self.leg_links[i].0.challenge_contribution(
                &eph_pk_participant,
                &enc_key_gen,
                &conf
                    .encryption
                    .ct_participant(conf.party_eph_pk.is_sender()),
                &mut transcript,
            )?;

            if conf.has_balance_decreased.is_some() {
                let eph_pk_base = conf.party_eph_pk.eph_pk_amount();
                self.leg_links[i]
                    .1
                    .as_ref()
                    .unwrap()
                    .challenge_contribution(
                        &eph_pk_base,
                        &comm_re_rand_gen,
                        &self.partial_ct_amounts[offset_amount],
                        &mut transcript,
                    )?;
                offset_amount += 1;
            }

            if !conf.encryption.is_asset_id_revealed() {
                // If asset id is not revealed in this leg
                let eph_pk_base = conf.party_eph_pk.eph_pk_asset_id().unwrap();
                match &self.leg_links[i].2 {
                    RespAssetId::Revealed => {
                        return Err(Error::ProofVerificationError(format!(
                            "Leg {i} has a hidden asset_id but auth proof marks it as revealed"
                        )));
                    }
                    RespAssetId::RevealedElsewhere(r) => {
                        // If asset id is not revealed in this leg but revealed in some other leg
                        if !is_asset_id_revealed {
                            return Err(Error::ProofVerificationError(format!(
                                "Leg {i}: auth proof claims asset_id is revealed elsewhere but no leg reveals it"
                            )));
                        }
                        let y = (conf.encryption.asset_id_ciphertext().unwrap() - h_at.unwrap())
                            .into_affine();
                        r.challenge_contribution(&eph_pk_base, &y, &mut transcript)?;
                    }
                    RespAssetId::Hidden(p) => {
                        // If asset id is not revealed in any leg
                        if is_asset_id_revealed {
                            return Err(Error::ProofVerificationError(format!(
                                "Leg {i}: auth proof treats asset_id as hidden but it is revealed in another leg"
                            )));
                        }
                        p.challenge_contribution(
                            &eph_pk_base,
                            &comm_re_rand_gen,
                            &self.partial_ct_asset_ids[offset_asset_id],
                            &mut transcript,
                        )?;
                        offset_asset_id += 1;
                    }
                }
            }
        }

        self.resp_enc_key_gen.challenge_contribution(
            &self.D,
            &comm_re_rand_gen,
            &enc_key_gen,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        verify_acc_comm(
            &self.partial_re_randomized_account_commitment,
            &self.t_re_randomized_account_commitment,
            &self.resp_re_randomized_account_commitment,
            &self.partial_updated_account_commitment,
            &self.t_updated_account_commitment,
            &self.resp_updated_account_commitment,
            &challenge,
            sk_gen,
            enc_key_gen,
            comm_re_rand_gen,
            rmc.as_deref_mut(),
        )?;

        let mut offset_amount = 0;
        let mut offset_asset_id = 0;

        for (i, (resp_participant, resp_amount, resp_asset_id)) in self.leg_links.iter().enumerate()
        {
            let conf = &legs_with_conf[i];
            let eph_pk_participant = conf.party_eph_pk.eph_pk_participant();

            verify_or_rmc_3!(
                rmc,
                resp_participant,
                format!("Participant proof is invalid at leg {i}"),
                conf.encryption
                    .ct_participant(conf.party_eph_pk.is_sender()),
                eph_pk_participant,
                enc_key_gen,
                &challenge,
                &self.resp_enc_key_gen.response1,
                &self.resp_re_randomized_account_commitment.0[1],
            );

            if conf.has_balance_decreased.is_some() {
                let eph_pk_base = conf.party_eph_pk.eph_pk_amount();
                let resp_amount_ref = resp_amount.as_ref().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Leg {i} has a balance change but auth proof is missing the amount response"
                    ))
                })?;
                verify_or_rmc_3!(
                    rmc,
                    resp_amount_ref,
                    format!("Amount proof is invalid at leg {i}"),
                    self.partial_ct_amounts[offset_amount],
                    eph_pk_base,
                    comm_re_rand_gen,
                    &challenge,
                    &self.resp_enc_key_gen.response1,
                );
                offset_amount += 1;
            }

            if !conf.encryption.is_asset_id_revealed() {
                // If asset id is not revealed in this leg
                let eph_pk_base = conf.party_eph_pk.eph_pk_asset_id().unwrap();
                match resp_asset_id {
                    RespAssetId::RevealedElsewhere(r) => {
                        let y = (conf.encryption.asset_id_ciphertext().unwrap() - h_at.unwrap())
                            .into_affine();
                        verify_or_rmc_2!(
                            rmc,
                            r,
                            format!("Asset id proof is invalid at leg {i}"),
                            y,
                            eph_pk_base,
                            &challenge,
                            &self.resp_enc_key_gen.response1,
                        );
                    }
                    RespAssetId::Hidden(p) => {
                        verify_or_rmc_3!(
                            rmc,
                            p,
                            format!("Asset id proof is invalid at leg {i}"),
                            self.partial_ct_asset_ids[offset_asset_id],
                            eph_pk_base,
                            comm_re_rand_gen,
                            &challenge,
                            &self.resp_enc_key_gen.response1,
                        );
                        offset_asset_id += 1;
                    }
                    _ => (),
                }
            }
        }

        verify_or_rmc_3!(
            rmc,
            self.resp_enc_key_gen,
            "Enc key gen proof is invalid",
            enc_key_gen,
            self.D,
            comm_re_rand_gen,
            &challenge,
        );
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub enum RespAssetId<G: AffineRepr> {
    /// If asset id is not revealed in this leg but revealed elsewhere when several legs are involved of same account
    RevealedElsewhere(PartialPokDiscreteLog<G>),
    /// If asset id is not revealed in any leg when several legs are involved of same account
    Hidden(Partial2PokPedersenCommitment<G>),
    /// If asset id is revealed in this leg
    Revealed,
}

mod serialization {
    use crate::auth_proofs::account::RespAssetId;
    use crate::auth_proofs::*;
    use ark_serialize::{Compress, SerializationError, Valid, Validate};
    use ark_std::io::Read;

    impl<G: AffineRepr> CanonicalSerialize for RespAssetId<G> {
        fn serialize_with_mode<W: Write>(
            &self,
            mut writer: W,
            compress: Compress,
        ) -> Result<(), SerializationError> {
            match self {
                RespAssetId::RevealedElsewhere(p) => {
                    0u8.serialize_with_mode(&mut writer, compress)?;
                    p.serialize_with_mode(&mut writer, compress)
                }
                RespAssetId::Hidden(p) => {
                    1u8.serialize_with_mode(&mut writer, compress)?;
                    p.serialize_with_mode(&mut writer, compress)
                }
                RespAssetId::Revealed => 2u8.serialize_with_mode(&mut writer, compress),
            }
        }

        fn serialized_size(&self, compress: Compress) -> usize {
            1 + match self {
                RespAssetId::RevealedElsewhere(p) => p.serialized_size(compress),
                RespAssetId::Hidden(p) => p.serialized_size(compress),
                RespAssetId::Revealed => 0,
            }
        }
    }

    impl<G: AffineRepr> CanonicalDeserialize for RespAssetId<G> {
        fn deserialize_with_mode<R: Read>(
            mut reader: R,
            compress: Compress,
            validate: Validate,
        ) -> Result<Self, SerializationError> {
            match u8::deserialize_with_mode(&mut reader, compress, validate)? {
                0 => Ok(RespAssetId::RevealedElsewhere(
                    PartialPokDiscreteLog::deserialize_with_mode(&mut reader, compress, validate)?,
                )),
                1 => Ok(RespAssetId::Hidden(
                    Partial2PokPedersenCommitment::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                )),
                2 => Ok(RespAssetId::Revealed),
                _ => Err(SerializationError::InvalidData),
            }
        }
    }

    impl<G: AffineRepr> Valid for RespAssetId<G> {
        fn check(&self) -> ark_std::result::Result<(), SerializationError> {
            match self {
                RespAssetId::RevealedElsewhere(p) => p.check(),
                RespAssetId::Hidden(p) => p.check(),
                RespAssetId::Revealed => Ok(()),
            }
        }
    }
}
