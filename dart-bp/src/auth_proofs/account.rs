use crate::account::common::leg_link::ensure_expected_leg_link_responses;
use crate::account::{LegProverConfig, LegVerifierConfig};
use crate::auth_proofs::helpers::{init_acc_comm_protocol, resp_acc_comm, verify_acc_comm};
use crate::auth_proofs::{AUTH_TXN_LABEL, DeviceTxnType, NULLIFIER_LABEL};
use crate::{
    ACCOUNT_COMMITMENT_LABEL, Error, LEG_ACTION_LABEL, LEG_ENC_LABEL, NONCE_LABEL,
    PARTY_EPH_PK_LABEL, RE_RANDOMIZED_PATH_LABEL, TXN_CHALLENGE_LABEL, add_to_transcript, dst,
    error,
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
//
// The auth proof additionally proves the participant relations, with responses owned entirely by this proof:
// ct_participant = S[0] * sk_enc^{-1} + enc_key_gen * sk_enc
// ct_participant_prime = S[0]' * sk_enc^{-1}
// where sk_enc^{-1} is `resp_enc_key_gen.response1` and sk_enc is
// `resp_re_randomized_account_commitment.0[1]`
// With the creation proofs' `ct_participant_prime = enc_key_gen * r_5` and `S[0]' = pk_s * r_5`, the
// second relation pins the leg party point to the affirming account's registered encryption key
// whenever `ct_participant_prime` is not identity.

/// For non-fee account related transactions, affirmation, counter update, reverse
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AuthProofAffirmation<G: AffineRepr> {
    /// The state (commitment) being invalidated through nullifier
    /// For Pedersen commitment to affirmation secret key, encryption secret key and part of
    /// randomness used to re-randomize the commitment. Carries the commitment to randomness `t`
    /// from step 1.
    pub resp_re_randomized_account_commitment: SchnorrResponse<G>,
    /// The new state (commitment) being created
    /// For Pedersen commitment to affirmation secret key, encryption secret key and a new
    /// randomness. Carries the commitment to randomness `t` from step 1.
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
    pub resp_D: Partial2PokPedersenCommitment<G>,
    pub resp_enc_key_gen: PokPedersenCommitment<G>,
    pub leg_links: Vec<LegAuthLink<G>>,
}

#[cfg_attr(
    all(test, feature = "nightly_mocking_tests"),
    mocktopus::macros::mockable
)]
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
        txn_type: &DeviceTxnType,
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
            txn_type,
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
        txn_type: &DeviceTxnType,
        sk_gen: G,
        enc_key_gen: G,
        comm_re_rand_gen: G, // generator used blind the old and new commitment parts
        enc_gen: G,
        mut transcript: &mut MerlinTranscript,
    ) -> error::Result<Self> {
        let sk_blinding = G::ScalarField::rand(rng);
        let sk_enc_blinding = G::ScalarField::rand(rng);
        let sk_enc_inv_blinding = G::ScalarField::rand(rng);
        let sk_enc_inv = Self::sk_enc_inverse(&sk_enc)?;
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
                LEG_ENC_LABEL,
                conf.encryption,
                PARTY_EPH_PK_LABEL,
                conf.party_eph_pk,
                LEG_ACTION_LABEL,
                conf.action_tag()
            );
        }
        txn_type.add_to_transcript(&mut transcript)?;

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
            dst::AUTH_ACC_COMM_OLD,
            dst::AUTH_ACC_COMM_NEW,
            &mut transcript,
        )?;

        let num_ct_amounts = legs_with_conf
            .iter()
            .filter(|c| c.needs_ct_amount())
            .count();
        if k_amounts.len() != num_ct_amounts {
            return Err(Error::ProofGenerationError(format!(
                "Expected {} k_amounts (one per leg needing ct_amount) but got {}",
                num_ct_amounts,
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

        let mut t_leg_link = Vec::with_capacity(legs_with_conf.len());

        enum AssetIdProtocol<G: AffineRepr> {
            /// Asset-id is hidden in this leg but revealed in some other leg
            Elsewhere(PokDiscreteLogProtocol<G>),
            /// Asset-id is hidden in this leg and all other legs
            Hidden(PokPedersenCommitmentProtocol<G>),
        }

        for conf in legs_with_conf {
            // ct_participant = Eph_participant * sk_enc^-1 + enc_key_gen * sk_enc and
            // ct_participant_prime = Eph_participant' * sk_enc^-1. Both responses are owned by this proof:
            // sk_enc^-1 is `resp_enc_key_gen.response1` and sk_enc is
            // `resp_re_randomized_account_commitment.0[1]`.
            let is_sender = conf.party_eph_pk.is_sender();
            let t_participant = PokPedersenCommitmentProtocol::init(
                sk_enc_inv,
                sk_enc_inv_blinding,
                &conf.party_eph_pk.eph_pk_participant(),
                sk_enc,
                sk_enc_blinding,
                &enc_key_gen,
            );
            t_participant.challenge_contribution(
                &conf.party_eph_pk.eph_pk_participant(),
                &enc_key_gen,
                &conf.encryption.ct_participant(is_sender),
                dst::AUTH_LEG_PARTICIPANT,
                &mut transcript,
            )?;
            let t_participant_prime = PokDiscreteLogProtocol::init(
                sk_enc_inv,
                sk_enc_inv_blinding,
                &conf.party_eph_pk.eph_pk_participant_prime(),
            );
            t_participant_prime.challenge_contribution(
                &conf.party_eph_pk.eph_pk_participant_prime(),
                &conf.encryption.ct_participant_prime(is_sender),
                dst::AUTH_LEG_PARTICIPANT_PRIME,
                &mut transcript,
            )?;

            // ct_amount_1 = Eph_amt * sk_enc^-1 + comm_re_rand_gen * k. Built only when the user
            // affirmation changes the balance. sk_enc^-1 is shared (resp_enc_key_gen.response1),
            // k is internal (response2) and canceled by the host's ct_amount_2.
            let t_amount = if conf.needs_ct_amount() {
                assert!(offset_amount < k_amounts.len());
                let eph_pk_base = conf.party_eph_pk.eph_pk_amount();
                partial_ct_amounts.push(
                    (comm_re_rand_gen * k_amounts[offset_amount] + eph_pk_base * sk_enc_inv)
                        .into_affine(),
                );
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
                    dst::AUTH_LEG_AMOUNT,
                    &mut transcript,
                )?;
                offset_amount += 1;
                Some(t_amount)
            } else {
                None
            };

            // ct_asset_id_1 when the asset-id is encrypted in this leg: Hidden (host supplies
            // ct_asset_id_2) when no leg reveals it, else a discrete-log proof against the
            // asset-id revealed in another leg.
            let t_asset_id = if !conf.is_asset_id_revealed() {
                // If asset id is not revealed in this leg
                let eph_pk_base = conf.party_eph_pk.eph_pk_asset_id().unwrap();
                if is_asset_id_revealed {
                    // If asset id is not revealed in this leg but revealed in some other leg
                    let t_asset_id =
                        PokDiscreteLogProtocol::init(sk_enc_inv, sk_enc_inv_blinding, &eph_pk_base);
                    let y = (conf.encryption.asset_id_ciphertext().unwrap() - h_at.unwrap())
                        .into_affine();
                    t_asset_id.challenge_contribution(
                        &eph_pk_base,
                        &y,
                        dst::AUTH_LEG_ASSET_ID_ELSEWHERE,
                        &mut transcript,
                    )?;
                    Some(AssetIdProtocol::Elsewhere(t_asset_id))
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
                            + eph_pk_base * sk_enc_inv)
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
                        dst::AUTH_LEG_ASSET_ID,
                        &mut transcript,
                    )?;
                    offset_asset_id += 1;
                    Some(AssetIdProtocol::Hidden(t_asset_id))
                }
            } else {
                None
            };

            t_leg_link.push((t_participant, t_participant_prime, t_amount, t_asset_id));
        }

        assert_eq!(offset_amount, k_amounts.len());
        assert_eq!(offset_asset_id, k_asset_ids.len());

        // For proving sk_enc^{-1} relation, create D = enc_key_gen * sk_e + B * r.
        // Now prove
        // D = enc_key_gen * sk_e + B * r
        // D * sk_enc^{-1} - B * r * sk_enc^{-1} = enc_gen
        let r = G::ScalarField::rand(rng);
        let D = (enc_key_gen * sk_enc + comm_re_rand_gen * r).into_affine();

        // The following is _likely expensive_ but clearer than trying to use one of leg encryption
        // components since there are many cases there and i have to write a different relation for
        // each case

        // For // D = enc_key_gen * sk_e + B * r
        let t_D = PokPedersenCommitmentProtocol::init(
            sk_enc,
            sk_enc_blinding,
            &enc_key_gen,
            r,
            G::ScalarField::rand(rng),
            &comm_re_rand_gen,
        );
        t_D.challenge_contribution(
            &enc_key_gen,
            &comm_re_rand_gen,
            &D,
            dst::AUTH_D,
            &mut transcript,
        )?;

        // For D * sk_enc^{-1} - B * r * sk_enc^{-1} = enc_gen
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
            dst::AUTH_ENC_KEY_GEN_INV,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let (resp_re_randomized_account_commitment, resp_updated_account_commitment) =
            resp_acc_comm(
                sk,
                sk_enc,
                rand_part_old_comm,
                rand_new_comm,
                &proto_old,
                &proto_new,
                &challenge,
            )?;

        let mut leg_links = Vec::with_capacity(t_leg_link.len());
        for (t_participant, t_participant_prime, t_amount, t_asset_id) in t_leg_link {
            leg_links.push(LegAuthLink {
                resp_participant: t_participant.gen_partial_proof(),
                resp_participant_prime: t_participant_prime.gen_partial_proof(),
                resp_amount: t_amount.map(|t| t.gen_partial2_proof(&challenge)),
                resp_asset_id: t_asset_id.map(|p| match p {
                    AssetIdProtocol::Elsewhere(d) => RespAssetId::Elsewhere(d.gen_partial_proof()),
                    AssetIdProtocol::Hidden(pc) => {
                        RespAssetId::Hidden(pc.gen_partial2_proof(&challenge))
                    }
                }),
            });
        }

        let resp_D = t_D.gen_partial2_proof(&challenge);
        let resp_enc_key_gen = t_enc_key_gen.gen_proof(&challenge);

        Ok(Self {
            resp_re_randomized_account_commitment,
            resp_updated_account_commitment,
            partial_re_randomized_account_commitment,
            partial_updated_account_commitment,
            partial_ct_amounts,
            partial_ct_asset_ids,
            D,
            resp_D,
            resp_enc_key_gen,
            leg_links,
        })
    }

    pub fn verify(
        &self,
        legs_conf: Vec<LegVerifierConfig<G>>,
        re_randomized_account_commitment: &G,
        updated_account_commitment: &G,
        nullifier: G,
        nonce: &[u8],
        txn_type: &DeviceTxnType,
        sk_gen: G,
        enc_key_gen: G,
        comm_re_rand_gen: G, // generator used blind the old and new commitment parts
        enc_gen: G,
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> error::Result<()> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);
        self.verify_with_given_transcript(
            legs_conf,
            re_randomized_account_commitment,
            updated_account_commitment,
            nullifier,
            nonce,
            txn_type,
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
        legs_conf: Vec<LegVerifierConfig<G>>,
        re_randomized_account_commitment: &G,
        updated_account_commitment: &G,
        nullifier: G,
        nonce: &[u8],
        txn_type: &DeviceTxnType,
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

        for conf in &legs_conf {
            add_to_transcript!(
                transcript,
                LEG_ENC_LABEL,
                conf.encryption,
                PARTY_EPH_PK_LABEL,
                conf.party_eph_pk,
                LEG_ACTION_LABEL,
                conf.action_tag()
            );
        }
        txn_type.add_to_transcript(&mut transcript)?;

        self.resp_re_randomized_account_commitment
            .challenge_contribution(dst::AUTH_ACC_COMM_OLD, &mut transcript)?;
        transcript.append(
            b"partial_acc_comm_old",
            &self.partial_re_randomized_account_commitment,
        );
        self.resp_updated_account_commitment
            .challenge_contribution(dst::AUTH_ACC_COMM_NEW, &mut transcript)?;
        transcript.append(
            b"partial_acc_comm_new",
            &self.partial_updated_account_commitment,
        );

        if legs_conf.len() != self.leg_links.len() {
            return Err(Error::ProofVerificationError(format!(
                "Needed {} leg proofs but got {}",
                legs_conf.len(),
                self.leg_links.len()
            )));
        }

        let num_ct_amounts = legs_conf.iter().filter(|l| l.needs_ct_amount()).count();
        if self.partial_ct_amounts.len() != num_ct_amounts {
            return Err(Error::ProofVerificationError(format!(
                "Invalid partial_ct_amounts length. Expected {}, got {}",
                num_ct_amounts,
                self.partial_ct_amounts.len()
            )));
        }

        let (asset_id, num_hidden) = LegVerifierConfig::asset_id_and_hidden_count(&legs_conf)?;

        let is_asset_id_revealed = asset_id.is_some();

        let num_hidden_asset_ids = if is_asset_id_revealed { 0 } else { num_hidden };
        if self.partial_ct_asset_ids.len() != num_hidden_asset_ids {
            return Err(Error::ProofVerificationError(format!(
                "Invalid partial_ct_asset_ids length. Expected {}, got {}",
                num_hidden_asset_ids,
                self.partial_ct_asset_ids.len()
            )));
        }

        let h_at = asset_id.map(|a| enc_gen * G::ScalarField::from(a));

        // `y = ct_asset_id - h_at` for every revealed-elsewhere leg, with one shared batch
        // normalization.
        let y_elsewhere = match h_at {
            Some(h_at) => <G as AffineRepr>::Group::normalize_batch(
                &legs_conf
                    .iter()
                    .zip(self.leg_links.iter())
                    .filter_map(|(conf, link)| {
                        match (
                            conf.is_asset_id_revealed(),
                            link.resp_asset_id.as_ref(),
                            conf.encryption.asset_id_ciphertext(),
                        ) {
                            (false, Some(RespAssetId::Elsewhere(_)), Some(ct)) => {
                                Some(ct.into_group() - h_at)
                            }
                            _ => None,
                        }
                    })
                    .collect::<Vec<_>>(),
            ),
            None => Vec::new(),
        };

        let mut offset_amount = 0;
        let mut offset_asset_id = 0;
        let mut elsewhere_idx = 0usize;

        for (i, (conf, link)) in legs_conf.iter().zip(self.leg_links.iter()).enumerate() {
            let is_sender = conf.party_eph_pk.is_sender();
            let ct_participant = conf.encryption.ct_participant(is_sender);
            let ct_participant_prime = conf.encryption.ct_participant_prime(is_sender);

            // `ct_participant_prime = enc_key_gen * r_5` (resp. `r_6`) is identity iff `r_5 = 0`, which
            // makes the second relation hold for any party point.
            if ct_participant_prime.is_zero() {
                return Err(Error::ProofVerificationError(format!(
                    "Leg {i}: ct_participant_prime is identity"
                )));
            }

            ensure_expected_leg_link_responses(
                i,
                link.resp_amount.is_some(),
                link.resp_asset_id.is_some(),
                conf.needs_ct_amount(),
                conf.is_asset_id_revealed(),
            )?;

            link.resp_participant.challenge_contribution(
                &conf.party_eph_pk.eph_pk_participant(),
                &enc_key_gen,
                &ct_participant,
                dst::AUTH_LEG_PARTICIPANT,
                &mut transcript,
            )?;
            link.resp_participant_prime.challenge_contribution(
                &conf.party_eph_pk.eph_pk_participant_prime(),
                &ct_participant_prime,
                dst::AUTH_LEG_PARTICIPANT_PRIME,
                &mut transcript,
            )?;

            if conf.needs_ct_amount() {
                let resp_amount = link.resp_amount.as_ref().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Leg {i} required amount proof but auth proof is missing it"
                    ))
                })?;
                let eph_pk_base = conf.party_eph_pk.eph_pk_amount();
                resp_amount.challenge_contribution(
                    &eph_pk_base,
                    &comm_re_rand_gen,
                    &self.partial_ct_amounts[offset_amount],
                    dst::AUTH_LEG_AMOUNT,
                    &mut transcript,
                )?;
                offset_amount += 1;
            }

            if !conf.is_asset_id_revealed() {
                // If asset id is not revealed in this leg
                let resp_asset_id = link.resp_asset_id.as_ref().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Leg {i} required asset-id proof but auth proof is missing it"
                    ))
                })?;
                let eph_pk_base = conf.party_eph_pk.eph_pk_asset_id().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Leg {i}: party_eph_pk is missing the asset-id ephemeral key but the leg hides the asset-id"
                    ))
                })?;
                match resp_asset_id {
                    RespAssetId::Elsewhere(r) => {
                        // If asset id is not revealed in this leg but revealed in some other leg
                        if !is_asset_id_revealed {
                            return Err(Error::ProofVerificationError(format!(
                                "Leg {i}: auth proof claims asset_id is revealed elsewhere but no leg reveals it"
                            )));
                        }
                        let _ = conf.encryption.asset_id_ciphertext().ok_or_else(|| {
                            Error::ProofVerificationError(format!(
                                "Leg {i}: encryption is missing the asset-id ciphertext but the leg hides the asset-id"
                            ))
                        })?;
                        let y = y_elsewhere[elsewhere_idx];
                        elsewhere_idx += 1;
                        r.challenge_contribution(
                            &eph_pk_base,
                            &y,
                            dst::AUTH_LEG_ASSET_ID_ELSEWHERE,
                            &mut transcript,
                        )?;
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
                            dst::AUTH_LEG_ASSET_ID,
                            &mut transcript,
                        )?;
                        offset_asset_id += 1;
                    }
                }
            }
        }

        self.resp_D.challenge_contribution(
            &enc_key_gen,
            &comm_re_rand_gen,
            &self.D,
            dst::AUTH_D,
            &mut transcript,
        )?;

        self.resp_enc_key_gen.challenge_contribution(
            &self.D,
            &comm_re_rand_gen,
            &enc_key_gen,
            dst::AUTH_ENC_KEY_GEN_INV,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        verify_acc_comm(
            &self.partial_re_randomized_account_commitment,
            &self.resp_re_randomized_account_commitment,
            &self.partial_updated_account_commitment,
            &self.resp_updated_account_commitment,
            &challenge,
            sk_gen,
            enc_key_gen,
            comm_re_rand_gen,
            rmc.as_deref_mut(),
        )?;

        let mut offset_amount = 0;
        let mut offset_asset_id = 0;
        let mut elsewhere_idx = 0usize;

        for (i, (conf, link)) in legs_conf.iter().zip(self.leg_links.iter()).enumerate() {
            // The participant relations share this proof's `sk_enc^-1`.
            let is_sender = conf.party_eph_pk.is_sender();
            verify_or_rmc_3!(
                rmc,
                link.resp_participant,
                format!("Participant ciphertext verification failed for leg {i}"),
                conf.encryption.ct_participant(is_sender),
                conf.party_eph_pk.eph_pk_participant(),
                enc_key_gen,
                &challenge,
                &self.resp_enc_key_gen.response1,
                &self.resp_re_randomized_account_commitment.0[1],
            );

            verify_or_rmc_2!(
                rmc,
                link.resp_participant_prime,
                format!("Participant prime ciphertext verification failed for leg {i}"),
                conf.encryption.ct_participant_prime(is_sender),
                conf.party_eph_pk.eph_pk_participant_prime(),
                &challenge,
                &self.resp_enc_key_gen.response1,
            );

            if conf.needs_ct_amount() {
                let resp_amount = link.resp_amount.as_ref().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Leg {i} required amount proof but auth proof is missing it"
                    ))
                })?;
                let eph_pk_base = conf.party_eph_pk.eph_pk_amount();
                verify_or_rmc_3!(
                    rmc,
                    resp_amount,
                    format!("Amount proof is invalid at leg {i}"),
                    self.partial_ct_amounts[offset_amount],
                    eph_pk_base,
                    comm_re_rand_gen,
                    &challenge,
                    &self.resp_enc_key_gen.response1,
                );
                offset_amount += 1;
            }

            if !conf.is_asset_id_revealed() {
                // If asset id is not revealed in this leg
                let resp_asset_id = link.resp_asset_id.as_ref().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Leg {i} required asset-id proof but auth proof is missing it"
                    ))
                })?;
                let eph_pk_base = conf.party_eph_pk.eph_pk_asset_id().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Leg {i}: party_eph_pk is missing the asset-id ephemeral key but the leg hides the asset-id"
                    ))
                })?;
                match resp_asset_id {
                    RespAssetId::Elsewhere(r) => {
                        let _ = conf.encryption.asset_id_ciphertext().ok_or_else(|| {
                            Error::ProofVerificationError(format!(
                                "Leg {i}: encryption is missing the asset-id ciphertext but the leg hides the asset-id"
                            ))
                        })?;
                        let y = y_elsewhere[elsewhere_idx];
                        elsewhere_idx += 1;
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
                }
            }
        }

        verify_or_rmc_3!(
            rmc,
            self.resp_D,
            "D proof is invalid",
            self.D,
            enc_key_gen,
            comm_re_rand_gen,
            &challenge,
            &self.resp_re_randomized_account_commitment.0[1],
        );

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

    /// Just for mocking
    pub(crate) fn sk_enc_inverse(sk_enc: &G::ScalarField) -> error::Result<G::ScalarField> {
        sk_enc.inverse().ok_or(Error::InvertingZero)
    }
}

#[derive(Clone, Debug)]
pub enum RespAssetId<G: AffineRepr> {
    /// asset-id revealed by another leg: `ct_asset_id - enc_gen * at = Eph_at * sk_enc^-1`
    Elsewhere(PartialPokDiscreteLog<G>),
    /// asset-id hidden in all legs: `ct_asset_id_1 = Eph_at * sk_enc^-1 + comm_re_rand_gen * k`
    Hidden(Partial2PokPedersenCommitment<G>),
}

/// Device side per-leg response for the split proof. The two participant relations
/// (`ct_participant = eph_pk_participant * sk_enc^-1 + enc_key_gen * sk_enc` and
/// `ct_participant_prime = eph_pk_participant_prime * sk_enc^-1`) are always present: `sk_enc^-1` is
/// `resp_enc_key_gen.response1` and `sk_enc` is `resp_re_randomized_account_commitment.0[1]`, so
/// both are owned by this proof. `ct_amount` is present if the balance changes and `ct_asset_id`
/// if the asset-id is encrypted in the leg.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegAuthLink<G: AffineRepr> {
    /// `ct_participant = Eph_s * sk_enc^-1 + enc_key_gen * sk_enc`, `sk_enc^-1` and `sk_enc` shared
    pub resp_participant: PartialPokPedersenCommitment<G>,
    /// `ct_participant_prime = Eph_s' * sk_enc^-1`, `sk_enc^-1` shared
    pub resp_participant_prime: PartialPokDiscreteLog<G>,
    /// `ct_amount_1 = Eph_amt * sk_enc^-1 + comm_re_rand_gen * k_1`, `sk_enc^-1` shared, `k_1` owned
    pub resp_amount: Option<Partial2PokPedersenCommitment<G>>,
    /// Hidden: `ct_asset_id_1 = Eph_at * sk_enc^-1 + comm_re_rand_gen * k_2`, `sk_enc^-1` shared, `k_2` owned
    /// Elsewhere: `ct_asset_id - enc_gen * at = Eph_at * sk_enc^-1`, `sk_enc^-1` shared
    pub resp_asset_id: Option<RespAssetId<G>>,
}

mod serialization {
    use crate::auth_proofs::account::RespAssetId;
    use crate::auth_proofs::*;
    use ark_serialize::{Compress, SerializationError, Valid, Validate};
    use ark_std::io::Read;
    use schnorr_pok::partial::Partial2PokPedersenCommitment;

    impl<G: AffineRepr> CanonicalSerialize for RespAssetId<G> {
        fn serialize_with_mode<W: Write>(
            &self,
            mut writer: W,
            compress: Compress,
        ) -> Result<(), SerializationError> {
            match self {
                RespAssetId::Elsewhere(p) => {
                    0u8.serialize_with_mode(&mut writer, compress)?;
                    p.serialize_with_mode(&mut writer, compress)
                }
                RespAssetId::Hidden(p) => {
                    1u8.serialize_with_mode(&mut writer, compress)?;
                    p.serialize_with_mode(&mut writer, compress)
                }
            }
        }

        fn serialized_size(&self, compress: Compress) -> usize {
            1 + match self {
                RespAssetId::Elsewhere(p) => p.serialized_size(compress),
                RespAssetId::Hidden(p) => p.serialized_size(compress),
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
                0 => Ok(RespAssetId::Elsewhere(
                    PartialPokDiscreteLog::deserialize_with_mode(&mut reader, compress, validate)?,
                )),
                1 => Ok(RespAssetId::Hidden(
                    Partial2PokPedersenCommitment::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                )),
                _ => Err(SerializationError::InvalidData),
            }
        }
    }

    impl<G: AffineRepr> Valid for RespAssetId<G> {
        fn check(&self) -> ark_std::result::Result<(), SerializationError> {
            match self {
                RespAssetId::Elsewhere(p) => p.check(),
                RespAssetId::Hidden(p) => p.check(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::account::PartyEphemeralPublicKey;
    use crate::auth_proofs::DeviceAffirmationType;
    use crate::keys::keygen_enc;
    use crate::leg::{Leg, LegEncConfig, LegEncCoreAndEphKeys, PartyVisibility};
    use crate::test_utils::crafted_party_point_leg;
    use ark_ec::short_weierstrass::Affine;
    use ark_pallas::{Fr, PallasConfig};
    use ark_std::UniformRand;
    use polymesh_dart_common::{AssetId, Balance};
    use rand::thread_rng;

    #[test]
    fn affirm_other_account_encryption_key() {
        // Standalone affirmation auth accepts this proof even when the consumed account key differs
        // from the leg key. The split verifier is the layer that checks the account leaf against the
        // proof's partial commitment.
        let mut rng = thread_rng();
        // Use independent bases so the mismatch is not hidden by setup.
        let sk_gen = Affine::<PallasConfig>::rand(&mut rng);
        let enc_key_gen = Affine::<PallasConfig>::rand(&mut rng);
        let comm_re_rand_gen = Affine::<PallasConfig>::rand(&mut rng);
        let enc_gen = Affine::<PallasConfig>::rand(&mut rng);

        let sk_e = Fr::rand(&mut rng);
        let sk_enc_e = Fr::rand(&mut rng);
        // Use a different encryption key for the leg sender.
        let (sk_enc_a_keys, ek_a) = keygen_enc(&mut rng, enc_key_gen);
        let sk_enc_a = sk_enc_a_keys.0;

        let amount = 100u64;
        let asset_id = 7u32;
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);
        let leg = Leg::new(ek_a.0, pk_r_e.0, amount, asset_id, vec![], vec![], vec![]).unwrap();
        let cfg = LegEncConfig {
            visibility: PartyVisibility::NoVisibility,
            reveal_asset_id: false,
        };
        let (leg_enc, _) = leg.encrypt(&mut rng, cfg, enc_key_gen, enc_gen).unwrap();
        let (leg_core, eph_pk_s) = leg_enc.core_and_eph_keys_for_sender();

        // The account leaf commits sk_enc_e, while the proof below is built with sk_enc_a.
        let rand_old = Fr::rand(&mut rng);
        let rand_new = Fr::rand(&mut rng);
        let pk_e = (sk_gen * sk_e + enc_key_gen * sk_enc_e).into_affine();
        let re_rand_leaf = (pk_e + comm_re_rand_gen * rand_old).into_affine();
        let updated_comm = (pk_e + comm_re_rand_gen * rand_new).into_affine();
        let nullifier = Affine::<PallasConfig>::rand(&mut rng);
        let nonce = b"acA1_split_gap";
        let k_amount = Fr::rand(&mut rng);
        let k_asset_id = Fr::rand(&mut rng);

        let legs = vec![LegProverConfig {
            encryption: leg_core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk_s.clone()),
            amount,
            has_balance_changed: true,
            has_counter_decreased: Some(false),
        }];
        let proof = AuthProofAffirmation::<Affine<PallasConfig>>::new(
            &mut rng,
            sk_e,
            sk_enc_a,
            rand_old,
            rand_new,
            vec![k_amount],
            vec![k_asset_id],
            legs,
            &re_rand_leaf,
            &updated_comm,
            nullifier,
            nonce,
            &DeviceTxnType::DeviceAffirmation {
                typ: DeviceAffirmationType::SenderAffirmation,
            },
            sk_gen,
            enc_key_gen,
            comm_re_rand_gen,
            enc_gen,
        )
        .unwrap();

        let conf = vec![LegVerifierConfig {
            encryption: leg_core,
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk_s),
            has_balance_decreased: Some(true),
            has_counter_decreased: Some(false),
        }];
        proof
            .verify(
                conf,
                &re_rand_leaf,
                &updated_comm,
                nullifier,
                nonce,
                &DeviceTxnType::DeviceAffirmation {
                    typ: DeviceAffirmationType::SenderAffirmation,
                },
                sk_gen,
                enc_key_gen,
                comm_re_rand_gen,
                enc_gen,
                None,
            )
            .unwrap();
    }

    #[test]
    fn auth_proof_binds_leg_action() {
        let mut rng = thread_rng();
        let sk_gen = Affine::<PallasConfig>::rand(&mut rng);
        let enc_key_gen = Affine::<PallasConfig>::rand(&mut rng);
        let comm_re_rand_gen = Affine::<PallasConfig>::rand(&mut rng);
        let enc_gen = Affine::<PallasConfig>::rand(&mut rng);

        let sk_e = Fr::rand(&mut rng);
        let (sk_enc, ek) = keygen_enc(&mut rng, enc_key_gen);
        let amount = 100u64;
        let asset_id = 7u32;
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);
        let leg = Leg::new(ek.0, pk_r_e.0, amount, asset_id, vec![], vec![], vec![]).unwrap();
        let cfg = LegEncConfig {
            visibility: PartyVisibility::NoVisibility,
            reveal_asset_id: false,
        };
        let (leg_enc, _) = leg.encrypt(&mut rng, cfg, enc_key_gen, enc_gen).unwrap();
        let (leg_core, eph_pk_s) = leg_enc.core_and_eph_keys_for_sender();

        let pk_e = (sk_gen * sk_e + enc_key_gen * sk_enc.0).into_affine();
        let rand_old = Fr::rand(&mut rng);
        let rand_new = Fr::rand(&mut rng);
        let re_rand_leaf = (pk_e + comm_re_rand_gen * rand_old).into_affine();
        let updated_comm = (pk_e + comm_re_rand_gen * rand_new).into_affine();
        let nullifier = Affine::<PallasConfig>::rand(&mut rng);
        let nonce = b"leg_action_binding";
        let k_amount = Fr::rand(&mut rng);
        let k_asset_id = Fr::rand(&mut rng);
        let txn_type = DeviceTxnType::DeviceAffirmation {
            typ: DeviceAffirmationType::SenderAffirmation,
        };

        let proof = AuthProofAffirmation::<Affine<PallasConfig>>::new(
            &mut rng,
            sk_e,
            sk_enc.0,
            rand_old,
            rand_new,
            vec![k_amount],
            vec![k_asset_id],
            vec![LegProverConfig {
                encryption: leg_core.clone(),
                party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk_s.clone()),
                amount,
                has_balance_changed: true,
                has_counter_decreased: Some(false),
            }],
            &re_rand_leaf,
            &updated_comm,
            nullifier,
            nonce,
            &txn_type,
            sk_gen,
            enc_key_gen,
            comm_re_rand_gen,
            enc_gen,
        )
        .unwrap();

        let verify = |has_counter_decreased: Option<bool>| {
            proof.verify(
                vec![LegVerifierConfig {
                    encryption: leg_core.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk_s.clone()),
                    has_balance_decreased: Some(true),
                    has_counter_decreased,
                }],
                &re_rand_leaf,
                &updated_comm,
                nullifier,
                nonce,
                &txn_type,
                sk_gen,
                enc_key_gen,
                comm_re_rand_gen,
                enc_gen,
                None,
            )
        };
        verify(Some(false)).unwrap();
        assert!(verify(Some(true)).is_err());
        assert!(verify(None).is_err());
    }

    const LEG_AMOUNT: Balance = 100;
    const LEG_ASSET_ID: AssetId = 7;

    /// Leg amount and asset-id of a leg made by `crafted_party_point_leg`, which the affirming
    /// party's key opens to `LEG_AMOUNT` of `LEG_ASSET_ID`.
    const CRAFTED_LEG_AMOUNT: Balance = 1000;
    const CRAFTED_LEG_ASSET_ID: AssetId = 8;

    /// Proves and verifies an affirmation of `LEG_AMOUNT` of `LEG_ASSET_ID` by the chosen party of a
    /// leg, made by `crafted_party_point_leg` when `crafted` and honestly otherwise. `tamper` changes
    /// the leg before proving.
    fn affirm_party_point_leg(
        is_sender: bool,
        reveal_asset_id: bool,
        crafted: bool,
        tamper: impl Fn(&mut LegEncCoreAndEphKeys<Affine<PallasConfig>>),
    ) -> error::Result<()> {
        let mut rng = thread_rng();
        let sk_gen = Affine::<PallasConfig>::rand(&mut rng);
        let enc_key_gen = Affine::<PallasConfig>::rand(&mut rng);
        let comm_re_rand_gen = Affine::<PallasConfig>::rand(&mut rng);
        let enc_gen = Affine::<PallasConfig>::rand(&mut rng);

        let sk = Fr::rand(&mut rng);
        let (sk_enc, ek) = keygen_enc(&mut rng, enc_key_gen);
        let (_, other_ek) = keygen_enc(&mut rng, enc_key_gen);
        let mut leg_enc = if crafted {
            let leg_asset_id = if reveal_asset_id {
                LEG_ASSET_ID
            } else {
                CRAFTED_LEG_ASSET_ID
            };
            crafted_party_point_leg(
                &mut rng,
                is_sender,
                sk_enc.0,
                other_ek.0,
                vec![],
                CRAFTED_LEG_AMOUNT,
                leg_asset_id,
                LEG_AMOUNT,
                LEG_ASSET_ID,
                reveal_asset_id,
                enc_key_gen,
                enc_gen,
            )
            .1
        } else {
            let (sender_pk, receiver_pk) = if is_sender {
                (ek.0, other_ek.0)
            } else {
                (other_ek.0, ek.0)
            };
            let leg = Leg::new(
                sender_pk,
                receiver_pk,
                LEG_AMOUNT,
                LEG_ASSET_ID,
                vec![],
                vec![],
                vec![],
            )
            .unwrap();
            let cfg = LegEncConfig {
                visibility: PartyVisibility::FullVisibility,
                reveal_asset_id,
            };
            leg.encrypt(&mut rng, cfg, enc_key_gen, enc_gen).unwrap().0
        };
        tamper(&mut leg_enc.leg_enc_core_and_eph_keys);
        let (leg_core, party_eph_pk) = if is_sender {
            let (core, eph_pk) = leg_enc.core_and_eph_keys_for_sender();
            (core, PartyEphemeralPublicKey::Sender(eph_pk))
        } else {
            let (core, eph_pk) = leg_enc.core_and_eph_keys_for_receiver();
            (core, PartyEphemeralPublicKey::Receiver(eph_pk))
        };

        let pk = (sk_gen * sk + enc_key_gen * sk_enc.0).into_affine();
        let rand_old = Fr::rand(&mut rng);
        let rand_new = Fr::rand(&mut rng);
        let re_rand_leaf = (pk + comm_re_rand_gen * rand_old).into_affine();
        let updated_comm = (pk + comm_re_rand_gen * rand_new).into_affine();
        let k_amounts = if is_sender {
            vec![Fr::rand(&mut rng)]
        } else {
            vec![]
        };
        let k_asset_ids = if reveal_asset_id {
            vec![]
        } else {
            vec![Fr::rand(&mut rng)]
        };
        let nullifier = Affine::<PallasConfig>::rand(&mut rng);
        let nonce = b"party_point_binding";
        let txn_type = DeviceTxnType::DeviceAffirmation {
            typ: if is_sender {
                DeviceAffirmationType::SenderAffirmation
            } else {
                DeviceAffirmationType::ReceiverAffirmation
            },
        };

        // The prover accepts the crafted point
        let proof = AuthProofAffirmation::new(
            &mut rng,
            sk,
            sk_enc.0,
            rand_old,
            rand_new,
            k_amounts,
            k_asset_ids,
            vec![LegProverConfig {
                encryption: leg_core.clone(),
                party_eph_pk: party_eph_pk.clone(),
                amount: LEG_AMOUNT,
                has_balance_changed: is_sender,
                has_counter_decreased: Some(false),
            }],
            &re_rand_leaf,
            &updated_comm,
            nullifier,
            nonce,
            &txn_type,
            sk_gen,
            enc_key_gen,
            comm_re_rand_gen,
            enc_gen,
        )
        .unwrap();

        proof.verify(
            vec![LegVerifierConfig {
                encryption: leg_core,
                party_eph_pk,
                has_balance_decreased: is_sender.then_some(true),
                has_counter_decreased: Some(false),
            }],
            &re_rand_leaf,
            &updated_comm,
            nullifier,
            nonce,
            &txn_type,
            sk_gen,
            enc_key_gen,
            comm_re_rand_gen,
            enc_gen,
            None,
        )
    }

    #[test]
    fn rejects_crafted_party_point() {
        // Only the second participant relation rejects the crafted point
        for is_sender in [true, false] {
            for reveal_asset_id in [true, false] {
                affirm_party_point_leg(is_sender, reveal_asset_id, false, |_| {}).unwrap();
                assert_err!(
                    affirm_party_point_leg(is_sender, reveal_asset_id, true, |_| {}),
                    Error::ProofVerificationError(_),
                    "Participant prime ciphertext verification failed"
                );
            }
        }
    }

    #[test]
    fn rejects_identity_participant_prime_ct() {
        // With `r_5 = 0` (resp. `r_6`) both prime points are identity and the second participant
        // relation holds for the crafted point
        for is_sender in [true, false] {
            for reveal_asset_id in [true, false] {
                assert_err!(
                    affirm_party_point_leg(is_sender, reveal_asset_id, true, |k| {
                        if is_sender {
                            k.core.ct_s_prime = Affine::zero();
                            k.eph_pk_s.r5 = Affine::zero();
                        } else {
                            k.core.ct_r_prime = Affine::zero();
                            k.eph_pk_r.r6 = Affine::zero();
                        }
                    }),
                    Error::ProofVerificationError(_),
                    "ct_participant_prime is identity"
                );
            }
        }
    }
}
