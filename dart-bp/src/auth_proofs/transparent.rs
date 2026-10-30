use crate::auth_proofs::account_comm_key::{AccountCommitmentKeyTrait, NUM_GENERATORS};
use crate::auth_proofs::helpers::{
    ensure_correct_updated_account_commitment, init_acc_comm_protocol,
    init_rand_new_comm_anchor_protocol, verify_acc_comm, verify_rand_new_comm_anchor,
};
use crate::auth_proofs::{AUTH_TXN_LABEL, DeviceTxnType, NULLIFIER_LABEL, helpers};
use crate::{
    ACCOUNT_COMMITMENT_LABEL, Error, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL, TXN_CHALLENGE_LABEL,
    add_to_transcript, dst, error::Result,
};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{UniformRand, vec::Vec};
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use schnorr_pok::SchnorrResponse;
use schnorr_pok::discrete_log::{PokDiscreteLogProtocol, PokPedersenCommitmentProtocol};
use schnorr_pok::partial::{
    Partial1PokPedersenCommitment, PartialPokDiscreteLog, PartialSchnorrResponse,
};
use zeroize::Zeroize;

// For new account commitment, auth proof will prove
// comm_new_1 = G_{Aff} * sk + G_{Enc} * sk_enc + B * r
// Host will prove
// comm_new_2 = ... + G_j * rho + G_k * rho^i + G_l * s + G_m * s^i + B * -r
// And verifier will check if comm_new_1 + comm_new_2 == comm_new (the final account commitment being inserted into tree)
// This is done as relations involving rho, rho^i, s, s_i need to be proven in BP
// Auth proof also proves rand_new_comm_anchor = anchor_gen * r and host proves
// -rand_new_comm_anchor = anchor_gen * -r, each sharing the response for r (resp. -r) with its part
// of comm_new, so comm_new has no B term.

/// For non-fee account related transparent transactions, like deposit and withdraw
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AuthProofTransparent<G: AffineRepr> {
    /// The state (commitment) being invalidated through nullifier
    /// For Pedersen commitment to affirmation secret key, encryption secret key and part of
    /// randomness used to re-randomize the commitment. Carries the commitment to randomness `t`
    /// from step 1.
    pub resp_re_randomized_account_commitment: SchnorrResponse<G>,
    /// The new state (commitment) being created
    /// For Pedersen commitment to affirmation secret key, encryption secret key and part of
    /// commitment randomness. Carries the commitment to randomness `t` from step 1.
    pub resp_updated_account_commitment: PartialSchnorrResponse<G>,
    /// `sk_gen * sk + enc_key_gen * sk_enc + comm_re_rand_gen * rand_part_old_comm`
    pub partial_re_randomized_account_commitment: G,
    /// `sk_gen * sk + enc_key_gen * sk_enc + comm_re_rand_gen * rand_new_comm`
    pub partial_updated_account_commitment: G,
    /// `anchor_gen * rand_new_comm`
    pub rand_new_comm_anchor: G,
    /// For `rand_new_comm_anchor = anchor_gen * rand_new_comm`. The response for `rand_new_comm` is in
    /// `resp_updated_account_commitment`.
    pub resp_rand_new_comm_anchor: PartialPokDiscreteLog<G>,
    resp_eph_pk: Vec<PartialPokDiscreteLog<G>>,
    resp_enc: Partial1PokPedersenCommitment<G>,
    pub encrypted_pubkeys: EncryptedPublicKey<G>,
}

impl<G: AffineRepr> AuthProofTransparent<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        sk: G::ScalarField,
        sk_enc: G::ScalarField,
        rand_part_old_comm: G::ScalarField, // part of commitment randomness used to re-randomize the old state commitment
        rand_new_comm: G::ScalarField, // new randomness used to blind this part of new account commitment
        // Opening of the new account commitment, in the order
        // `[balance, counter, asset_id, rho, current_rho, randomness, current_randomness, id]`
        new_acc_openings: [G::ScalarField; NUM_GENERATORS - 2],
        re_randomized_account_commitment: &G,
        updated_account_commitment: &G,
        nullifier: G,
        auditor_keys: Vec<G>,
        nonce: &[u8], // This could be the same nonce used by host device or a concatenation of host's nonce and other data like its challenge (if doing sequential)
        txn_type: &DeviceTxnType,
        comm_re_rand_gen: G, // generator used blind the old and new commitment parts
        anchor_gen: G,       // generator for the public anchor of `rand_new_comm`
        account_comm_key: &impl AccountCommitmentKeyTrait<G>,
    ) -> Result<Self> {
        let sk_gen = account_comm_key.sk_gen();
        let enc_key_gen = account_comm_key.sk_enc_gen();
        ensure_correct_updated_account_commitment(
            sk,
            sk_enc,
            updated_account_commitment,
            &new_acc_openings,
            account_comm_key,
        )?;

        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);

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
        txn_type.add_to_transcript(&mut transcript)?;

        let sk_blinding = G::ScalarField::rand(rng);
        let sk_enc_blinding = G::ScalarField::rand(rng);

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
            dst::TRANSPARENT_AUTH_ACC_COMM_OLD,
            dst::TRANSPARENT_AUTH_ACC_COMM_NEW,
            &mut transcript,
        )?;
        let (proto_anchor, rand_new_comm_anchor) = init_rand_new_comm_anchor_protocol(
            rand_new_comm,
            &proto_new,
            anchor_gen,
            dst::TRANSPARENT_AUTH_ACC_COMM_NEW_ANCHOR,
            &mut transcript,
        )?;

        let (t_eph_pk, t_enc, encrypted_pubkey) = init_pk_enc_protocol(
            rng,
            sk,
            sk_blinding,
            auditor_keys,
            sk_gen,
            enc_key_gen,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let (resp_eph_pk, reps_enc) = reps_pk_enc(t_eph_pk, t_enc, &challenge);
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

        Ok(Self {
            resp_re_randomized_account_commitment,
            resp_updated_account_commitment,
            partial_re_randomized_account_commitment,
            partial_updated_account_commitment,
            rand_new_comm_anchor,
            resp_rand_new_comm_anchor: proto_anchor.gen_partial_proof(),
            resp_eph_pk,
            resp_enc: reps_enc,
            encrypted_pubkeys: encrypted_pubkey,
        })
    }

    pub fn verify(
        &self,
        re_randomized_account_commitment: &G,
        updated_account_commitment: &G,
        nullifier: G,
        auditor_keys: &[G],
        nonce: &[u8],
        txn_type: &DeviceTxnType,
        sk_gen: G,
        enc_key_gen: G,
        comm_re_rand_gen: G, // generator used blind the old and new commitment parts
        anchor_gen: G,       // generator for the public anchor of `rand_new_comm`
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);

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
        txn_type.add_to_transcript(&mut transcript)?;

        self.challenge_contribution(
            &auditor_keys,
            sk_gen,
            enc_key_gen,
            anchor_gen,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        self.verify_given_challenge(
            auditor_keys,
            sk_gen,
            enc_key_gen,
            comm_re_rand_gen,
            anchor_gen,
            &challenge,
            rmc,
        )
    }

    pub fn challenge_contribution(
        &self,
        auditor_keys: &[G],
        sk_gen: G,
        enc_key_gen: G,
        anchor_gen: G,
        transcript: &mut MerlinTranscript,
    ) -> Result<()> {
        self.resp_re_randomized_account_commitment
            .challenge_contribution(dst::TRANSPARENT_AUTH_ACC_COMM_OLD, transcript)?;
        transcript.append(
            b"partial_acc_comm_old",
            &self.partial_re_randomized_account_commitment,
        );
        self.resp_updated_account_commitment
            .challenge_contribution(dst::TRANSPARENT_AUTH_ACC_COMM_NEW, transcript)?;
        transcript.append(
            b"partial_acc_comm_new",
            &self.partial_updated_account_commitment,
        );
        self.resp_rand_new_comm_anchor.challenge_contribution(
            &anchor_gen,
            &self.rand_new_comm_anchor,
            dst::TRANSPARENT_AUTH_ACC_COMM_NEW_ANCHOR,
            transcript,
        )?;

        chal_contrib_pk_enc(
            &self.resp_eph_pk,
            &self.resp_enc,
            &self.encrypted_pubkeys,
            auditor_keys,
            sk_gen,
            enc_key_gen,
            transcript,
        )?;

        Ok(())
    }

    pub fn verify_given_challenge(
        &self,
        auditor_keys: &[G],
        sk_gen: G,
        enc_key_gen: G,
        comm_re_rand_gen: G,
        anchor_gen: G,
        challenge: &G::ScalarField,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        verify_acc_comm(
            &self.partial_re_randomized_account_commitment,
            &self.resp_re_randomized_account_commitment,
            &self.partial_updated_account_commitment,
            &self.resp_updated_account_commitment,
            challenge,
            sk_gen,
            enc_key_gen,
            comm_re_rand_gen,
            rmc.as_deref_mut(),
        )?;
        verify_rand_new_comm_anchor(
            self.rand_new_comm_anchor,
            &self.resp_rand_new_comm_anchor,
            &self.resp_updated_account_commitment,
            challenge,
            anchor_gen,
            rmc.as_deref_mut(),
        )?;

        // Verify pk encryption proofs (sk_response is index 0 from old commitment's full response)
        verify_pk_enc(
            &self.resp_eph_pk,
            &self.resp_enc,
            &self.encrypted_pubkeys,
            auditor_keys,
            challenge,
            &self.resp_re_randomized_account_commitment.0[0],
            sk_gen,
            enc_key_gen,
            rmc,
        )?;

        Ok(())
    }
}

/// Public key of an account encrypted for auditors/mediators using twisted-Elgamal
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct EncryptedPublicKey<G: AffineRepr> {
    /// Ephemeral key per auditor/mediator like `r * PK_i`
    pub eph_pk: Vec<G>,
    /// Encrypted account public key as `r * G + pk_{acct}`
    pub encrypted: G,
}

impl<G: AffineRepr> EncryptedPublicKey<G> {
    /// Decrypt to the get the public key of account using auditor/mediator secret key
    pub fn decrypt(&self, index: usize, mut sk: G::ScalarField) -> G {
        assert!(index < self.eph_pk.len());
        sk.inverse_in_place().unwrap();
        let mask = self.eph_pk[index] * sk;
        sk.zeroize();
        (self.encrypted - mask).into_affine()
    }
}

pub fn init_pk_enc_protocol<R: CryptoRngCore, G: AffineRepr>(
    rng: &mut R,
    sk: G::ScalarField,
    sk_blinding: G::ScalarField,
    auditor_keys: Vec<G>,
    sk_gen: G,
    enc_key_gen: G,
    transcript: &mut MerlinTranscript,
) -> Result<(
    Vec<PokDiscreteLogProtocol<G>>,
    PokPedersenCommitmentProtocol<G>,
    EncryptedPublicKey<G>,
)> {
    let mut r = G::ScalarField::rand(rng);
    let mut r_blinding = G::ScalarField::rand(rng);
    let eph_pk =
        G::Group::normalize_batch(&auditor_keys.iter().map(|pk| *pk * r).collect::<Vec<_>>());
    let encrypted = (enc_key_gen * r + sk_gen * sk).into_affine();

    let t_enc =
        PokPedersenCommitmentProtocol::init(r, r_blinding, &enc_key_gen, sk, sk_blinding, &sk_gen);
    let t_eph_pk = auditor_keys
        .iter()
        .map(|pk| PokDiscreteLogProtocol::init(r, r_blinding, pk))
        .collect::<Vec<_>>();

    let encrypted_pubkey = EncryptedPublicKey { eph_pk, encrypted };
    transcript.append(b"encrypted_pubkey", &encrypted_pubkey);
    t_enc.challenge_contribution(
        &enc_key_gen,
        &sk_gen,
        &encrypted_pubkey.encrypted,
        dst::TRANSPARENT_ENC_PUBKEY_ENC,
        transcript,
    )?;
    for (i, t) in t_eph_pk.iter().enumerate() {
        t.challenge_contribution(
            &auditor_keys[i],
            &encrypted_pubkey.eph_pk[i],
            dst::TRANSPARENT_ENC_PUBKEY_EPH,
            transcript,
        )?;
    }

    r.zeroize();
    r_blinding.zeroize();
    Ok((t_eph_pk, t_enc, encrypted_pubkey))
}

pub fn reps_pk_enc<G: AffineRepr>(
    t_eph_pk: Vec<PokDiscreteLogProtocol<G>>,
    t_enc: PokPedersenCommitmentProtocol<G>,
    challenge: &G::ScalarField,
) -> (
    Vec<PartialPokDiscreteLog<G>>,
    Partial1PokPedersenCommitment<G>,
) {
    let resp_enc = t_enc.gen_partial1_proof(challenge);
    let resp_eph_pk = t_eph_pk
        .into_iter()
        .map(|t| t.gen_partial_proof())
        .collect::<Vec<_>>();
    (resp_eph_pk, resp_enc)
}

pub fn chal_contrib_pk_enc<G: AffineRepr>(
    resp_eph_pk: &[PartialPokDiscreteLog<G>],
    resp_enc: &Partial1PokPedersenCommitment<G>,
    encrypted_pubkey: &EncryptedPublicKey<G>,
    auditor_keys: &[G],
    sk_gen: G,
    enc_key_gen: G,
    transcript: &mut MerlinTranscript,
) -> Result<()> {
    if encrypted_pubkey.eph_pk.len() != auditor_keys.len() {
        return Err(Error::EncryptionOrProofsNotPresentForAllKeys(
            encrypted_pubkey.eph_pk.len(),
            auditor_keys.len(),
        ));
    }
    if resp_eph_pk.len() != auditor_keys.len() {
        return Err(Error::EncryptionOrProofsNotPresentForAllKeys(
            resp_eph_pk.len(),
            auditor_keys.len(),
        ));
    }

    transcript.append(b"encrypted_pubkey", &encrypted_pubkey);
    resp_enc.challenge_contribution(
        &enc_key_gen,
        &sk_gen,
        &encrypted_pubkey.encrypted,
        dst::TRANSPARENT_ENC_PUBKEY_ENC,
        transcript,
    )?;
    for (i, r) in resp_eph_pk.iter().enumerate() {
        r.challenge_contribution(
            &auditor_keys[i],
            &encrypted_pubkey.eph_pk[i],
            dst::TRANSPARENT_ENC_PUBKEY_EPH,
            transcript,
        )?;
    }

    Ok(())
}

pub fn verify_pk_enc<G: AffineRepr>(
    resp_eph_pk: &[PartialPokDiscreteLog<G>],
    resp_enc: &Partial1PokPedersenCommitment<G>,
    encrypted_pubkey: &EncryptedPublicKey<G>,
    auditor_keys: &[G],
    challenge: &G::ScalarField,
    sk_response: &G::ScalarField,
    sk_gen: G,
    enc_key_gen: G,
    mut rmc: Option<&mut RandomizedMultChecker<G>>,
) -> Result<()> {
    if encrypted_pubkey.eph_pk.len() != auditor_keys.len() {
        return Err(Error::EncryptionOrProofsNotPresentForAllKeys(
            encrypted_pubkey.eph_pk.len(),
            auditor_keys.len(),
        ));
    }
    if resp_eph_pk.len() != auditor_keys.len() {
        return Err(Error::EncryptionOrProofsNotPresentForAllKeys(
            resp_eph_pk.len(),
            auditor_keys.len(),
        ));
    }
    verify_or_rmc_3!(
        rmc,
        resp_enc,
        "Account public key encryption verification failed",
        encrypted_pubkey.encrypted,
        enc_key_gen,
        sk_gen,
        challenge,
        sk_response,
    );
    for (i, r) in resp_eph_pk.iter().enumerate() {
        verify_or_rmc_2!(
            rmc,
            r,
            "Ephemeral public key encryption verification failed",
            encrypted_pubkey.eph_pk[i],
            auditor_keys[i],
            &challenge,
            &resp_enc.response1,
        );
    }
    Ok(())
}
