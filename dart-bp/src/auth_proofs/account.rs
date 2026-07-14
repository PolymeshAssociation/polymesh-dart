use crate::account::{LegProverConfig, LegVerifierConfig};
use crate::auth_proofs::helpers::{init_acc_comm_protocol, resp_acc_comm, verify_acc_comm};
use crate::auth_proofs::{AUTH_TXN_LABEL, NULLIFIER_LABEL};
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
    Partial2PokPedersenCommitment, PartialPokDiscreteLog, PartialSchnorrResponse,
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
                LEG_ENCRYPTION_LABEL,
                conf.encryption,
                PARTY_EPH_PK_LABEL,
                conf.party_eph_pk
            );
        }

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
            // ct_amount_1 = Eph_amt * sk_enc^-1 + comm_re_rand_gen * k. Built when the leg reveals
            // its asset-id or user affirmation changes balance. sk_enc^-1 is shared (resp_enc_key_gen.response1),
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
                    t_asset_id.challenge_contribution(&eph_pk_base, &y, &mut transcript)?;
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
                        &mut transcript,
                    )?;
                    offset_asset_id += 1;
                    Some(AssetIdProtocol::Hidden(t_asset_id))
                }
            } else {
                None
            };

            t_leg_link.push((t_amount, t_asset_id));
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
        t_D.challenge_contribution(&enc_key_gen, &comm_re_rand_gen, &D, &mut transcript)?;

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
        for (t_amount, t_asset_id) in t_leg_link {
            let resp_amount = t_amount.map(|t| t.gen_partial2_proof(&challenge));
            let resp_asset_id = t_asset_id.map(|p| match p {
                AssetIdProtocol::Elsewhere(d) => RespAssetId::Elsewhere(d.gen_partial_proof()),
                AssetIdProtocol::Hidden(pc) => {
                    RespAssetId::Hidden(pc.gen_partial2_proof(&challenge))
                }
            });
            let link = match (resp_amount, resp_asset_id) {
                (Some(resp_amount), None) => LegAuthLink::AmountOnly { resp_amount },
                (None, Some(resp_asset_id)) => LegAuthLink::AssetIdOnly { resp_asset_id },
                (Some(resp_amount), Some(resp_asset_id)) => LegAuthLink::AssetIdAndAmount {
                    resp_asset_id,
                    resp_amount,
                },
                _ => {
                    return Err(Error::ProofGenerationError(
                        "Leg has neither ct_amount nor ct_asset_id to tie it to the account"
                            .to_string(),
                    ));
                }
            };
            leg_links.push(link);
        }

        let resp_D = t_D.gen_partial2_proof(&challenge);
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

        let mut offset_amount = 0;
        let mut offset_asset_id = 0;

        for (i, (conf, link)) in legs_conf.iter().zip(self.leg_links.iter()).enumerate() {
            if conf.needs_ct_amount() {
                let resp_amount = link.resp_amount().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Leg {i} required amount proof but auth proof is missing it"
                    ))
                })?;
                let eph_pk_base = conf.party_eph_pk.eph_pk_amount();
                resp_amount.challenge_contribution(
                    &eph_pk_base,
                    &comm_re_rand_gen,
                    &self.partial_ct_amounts[offset_amount],
                    &mut transcript,
                )?;
                offset_amount += 1;
            }

            if !conf.is_asset_id_revealed() {
                // If asset id is not revealed in this leg
                let resp_asset_id = link.resp_asset_id().ok_or_else(|| {
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
                        let y = (conf.encryption.asset_id_ciphertext().ok_or_else(|| {
                            Error::ProofVerificationError(format!(
                                "Leg {i}: encryption is missing the asset-id ciphertext but the leg hides the asset-id"
                            ))
                        })? - h_at.unwrap())
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

        self.resp_D.challenge_contribution(
            &enc_key_gen,
            &comm_re_rand_gen,
            &self.D,
            &mut transcript,
        )?;

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

        for (i, (conf, link)) in legs_conf.iter().zip(self.leg_links.iter()).enumerate() {
            if conf.needs_ct_amount() {
                let resp_amount = link.resp_amount().ok_or_else(|| {
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
                let resp_asset_id = link.resp_asset_id().ok_or_else(|| {
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
                        let y = (conf.encryption.asset_id_ciphertext().ok_or_else(|| {
                            Error::ProofVerificationError(format!(
                                "Leg {i}: encryption is missing the asset-id ciphertext but the leg hides the asset-id"
                            ))
                        })? - h_at.unwrap())
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

/// Device side per-leg response for the split proof. The variant depends on whether the leg
/// reveals its asset-id and whether the balance changes, like `LegAccountLink` for the solo proof.
#[derive(Clone, Debug)]
pub enum LegAuthLink<G: AffineRepr> {
    /// asset-id revealed in this leg
    AmountOnly {
        /// `ct_amount_1 = Eph_amt * sk_enc^-1 + comm_re_rand_gen * k_1`, `sk_enc^-1` shared, `k_1` owned
        resp_amount: Partial2PokPedersenCommitment<G>,
    },
    /// asset-id encrypted, balance unchanged
    AssetIdOnly {
        /// Hidden: `ct_asset_id_1 = Eph_at * sk_enc^-1 + comm_re_rand_gen * k_2`, `sk_enc^-1` shared, `k_2` owned
        /// Elsewhere: `ct_asset_id - enc_gen * at = Eph_at * sk_enc^-1`, `sk_enc^-1` shared
        resp_asset_id: RespAssetId<G>,
    },
    /// asset-id encrypted, balance changed
    AssetIdAndAmount {
        /// Hidden: `ct_asset_id_1 = Eph_at * sk_enc^-1 + comm_re_rand_gen * k_2`, `sk_enc^-1` shared, `k_2` owned
        /// Elsewhere: `ct_asset_id - enc_gen * at = Eph_at * sk_enc^-1`, `sk_enc^-1` shared
        resp_asset_id: RespAssetId<G>,
        /// `ct_amount_1 = Eph_amt * sk_enc^-1 + comm_re_rand_gen * k_1`, `sk_enc^-1` shared, `k_1` owned
        resp_amount: Partial2PokPedersenCommitment<G>,
    },
}

impl<G: AffineRepr> LegAuthLink<G> {
    pub fn resp_amount(&self) -> Option<&Partial2PokPedersenCommitment<G>> {
        match self {
            Self::AmountOnly { resp_amount } => Some(resp_amount),
            Self::AssetIdAndAmount { resp_amount, .. } => Some(resp_amount),
            Self::AssetIdOnly { .. } => None,
        }
    }

    pub fn resp_asset_id(&self) -> Option<&RespAssetId<G>> {
        match self {
            Self::AssetIdOnly { resp_asset_id } => Some(resp_asset_id),
            Self::AssetIdAndAmount { resp_asset_id, .. } => Some(resp_asset_id),
            Self::AmountOnly { .. } => None,
        }
    }
}

mod serialization {
    use crate::auth_proofs::account::{LegAuthLink, RespAssetId};
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

    impl<G: AffineRepr> CanonicalSerialize for LegAuthLink<G> {
        fn serialize_with_mode<W: Write>(
            &self,
            mut writer: W,
            compress: Compress,
        ) -> Result<(), SerializationError> {
            match self {
                LegAuthLink::AmountOnly { resp_amount } => {
                    0u8.serialize_with_mode(&mut writer, compress)?;
                    resp_amount.serialize_with_mode(&mut writer, compress)
                }
                LegAuthLink::AssetIdOnly { resp_asset_id } => {
                    1u8.serialize_with_mode(&mut writer, compress)?;
                    resp_asset_id.serialize_with_mode(&mut writer, compress)
                }
                LegAuthLink::AssetIdAndAmount {
                    resp_asset_id,
                    resp_amount,
                } => {
                    2u8.serialize_with_mode(&mut writer, compress)?;
                    resp_asset_id.serialize_with_mode(&mut writer, compress)?;
                    resp_amount.serialize_with_mode(&mut writer, compress)
                }
            }
        }

        fn serialized_size(&self, compress: Compress) -> usize {
            1 + match self {
                LegAuthLink::AmountOnly { resp_amount } => resp_amount.serialized_size(compress),
                LegAuthLink::AssetIdOnly { resp_asset_id } => {
                    resp_asset_id.serialized_size(compress)
                }
                LegAuthLink::AssetIdAndAmount {
                    resp_asset_id,
                    resp_amount,
                } => {
                    resp_asset_id.serialized_size(compress) + resp_amount.serialized_size(compress)
                }
            }
        }
    }

    impl<G: AffineRepr> CanonicalDeserialize for LegAuthLink<G> {
        fn deserialize_with_mode<R: Read>(
            mut reader: R,
            compress: Compress,
            validate: Validate,
        ) -> Result<Self, SerializationError> {
            match u8::deserialize_with_mode(&mut reader, compress, validate)? {
                0 => Ok(LegAuthLink::AmountOnly {
                    resp_amount: Partial2PokPedersenCommitment::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                }),
                1 => Ok(LegAuthLink::AssetIdOnly {
                    resp_asset_id: RespAssetId::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                }),
                2 => Ok(LegAuthLink::AssetIdAndAmount {
                    resp_asset_id: RespAssetId::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                    resp_amount: Partial2PokPedersenCommitment::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                }),
                _ => Err(SerializationError::InvalidData),
            }
        }
    }

    impl<G: AffineRepr> Valid for LegAuthLink<G> {
        fn check(&self) -> ark_std::result::Result<(), SerializationError> {
            match self {
                LegAuthLink::AmountOnly { resp_amount } => resp_amount.check(),
                LegAuthLink::AssetIdOnly { resp_asset_id } => resp_asset_id.check(),
                LegAuthLink::AssetIdAndAmount {
                    resp_asset_id,
                    resp_amount,
                } => {
                    resp_asset_id.check()?;
                    resp_amount.check()
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::account::PartyEphemeralPublicKey;
    use crate::keys::keygen_enc;
    use crate::leg::{Leg, LegEncConfig};
    use ark_ec::short_weierstrass::Affine;
    use ark_pallas::{Fr, PallasConfig};
    use ark_std::UniformRand;
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
            parties_see_each_other: false,
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
                sk_gen,
                enc_key_gen,
                comm_re_rand_gen,
                enc_gen,
                None,
            )
            .unwrap();
    }
}
