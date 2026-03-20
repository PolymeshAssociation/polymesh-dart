use crate::account::{AccountCommitmentKeyTrait, AccountState, AccountStateCommitment};
use crate::leg::LegEncryption;
use crate::{
    ACCOUNT_COMMITMENT_LABEL, ASSET_ID_LABEL, BALANCE_LABEL, Error, ID_LABEL, NONCE_LABEL,
    PK_LABEL, TXN_CHALLENGE_LABEL, add_to_transcript, error::Result,
};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::collections::BTreeSet;
use ark_std::ops::Neg;
use ark_std::string::ToString;
use ark_std::{format, vec, vec::Vec};
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{AssetId, Balance, PendingTxnCounter};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{PokDiscreteLog, PokDiscreteLogProtocol};
use schnorr_pok::partial::PartialPokDiscreteLog;
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};

// TODO: PoB can also benefit from RandomizedMultChecker but not doing it for now

pub const COUNTER_LABEL: &'static [u8; 7] = b"counter";
pub const LEGS_LABEL: &'static [u8; 4] = b"legs";
pub const TXN_POB_LABEL: &[u8; 20] = b"proof-of-balance-txn";
pub const PENDING_SENT_AMOUNT_LABEL: &'static [u8; 19] = b"pending_sent_amount";
pub const PENDING_RECV_AMOUNT_LABEL: &'static [u8; 19] = b"pending_recv_amount";

/// This is the proof for doing proof of balance with an auditor. This reveals the ID for proof efficiency as the public key is already revealed.
/// Uses Batch Schnorr protocol from Fig. 2 of [this paper](https://iacr.org/archive/asiacrypt2004/33290273/33290273.pdf)
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PobWithAuditorProof<G: AffineRepr> {
    pub nullifier: G,
    pub t_acc: G,
    pub resp_acc: SchnorrResponse<G>,
    pub resp_null: PartialPokDiscreteLog<G>,
    pub resp_pk: PokDiscreteLog<G>,
}

impl<G: AffineRepr> PobWithAuditorProof<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        pk: &G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<Self> {
        let transcript = MerlinTranscript::new(TXN_POB_LABEL);
        Self::new_with_given_transcript(
            rng,
            pk,
            account,
            account_commitment,
            nonce,
            account_comm_key,
            transcript,
        )
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        pk: &G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        mut transcript: MerlinTranscript,
    ) -> Result<Self> {
        // Need to prove that:
        // 1. sk used in commitment is for the revealed pk
        // 2. nullifier is created from current_rho
        //
        // The prover should share the index of account commitment in tree so verifier can efficiently fetch the commitment and compare. If its not possible then do a membership proof

        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            ID_LABEL,
            account.id,
            PK_LABEL,
            pk
        );

        let null_gen = account_comm_key.current_rho_gen();
        let pk_gen = account_comm_key.sk_gen();

        let nullifier = account.nullifier(&account_comm_key);

        let sk_blinding = G::ScalarField::rand(rng);
        let current_rho_blinding = G::ScalarField::rand(rng);

        // For proving relation g_i * rho + g_j * current_rho + g_k * randomness + g_k2 * current_randomness + g_l * sk_enc_inv = C - (pk + g_a * v + g_b * at + g_c * cnt + g_d * id)
        // where C is the account commitment and rho, current_rho, randomness, current_randomness, sk_enc_inv are the witness, rest are instance
        let t_acc = SchnorrCommitment::new(
            &[
                account_comm_key.rho_gen(),
                null_gen,
                account_comm_key.randomness_gen(),
                account_comm_key.current_randomness_gen(),
                account_comm_key.sk_enc_gen(),
            ],
            vec![
                G::ScalarField::rand(rng),
                current_rho_blinding,
                G::ScalarField::rand(rng),
                G::ScalarField::rand(rng),
                G::ScalarField::rand(rng),
            ],
        );
        let t_null =
            PokDiscreteLogProtocol::init(account.current_rho, current_rho_blinding, &null_gen);

        let t_pk = PokDiscreteLogProtocol::init(account.sk, sk_blinding, &pk_gen);

        t_acc.challenge_contribution(&mut transcript)?;
        t_null.challenge_contribution(&null_gen, &nullifier, &mut transcript)?;
        t_pk.challenge_contribution(&pk_gen, &pk, &mut transcript)?;

        let prover_challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let resp_acc = t_acc.response(
            &[
                account.rho,
                account.current_rho,
                account.randomness,
                account.current_randomness,
                account.sk_enc_inv,
            ],
            &prover_challenge,
        )?;
        let resp_null = t_null.gen_partial_proof();
        let resp_pk = t_pk.gen_proof(&prover_challenge);
        Ok(Self {
            nullifier,
            t_acc: t_acc.t,
            resp_acc,
            resp_null,
            resp_pk,
        })
    }

    pub fn verify(
        &self,
        asset_id: AssetId,
        balance: Balance,
        counter: PendingTxnCounter,
        id: G::ScalarField,
        pk: &G,
        account_commitment: AccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<()> {
        let transcript = MerlinTranscript::new(TXN_POB_LABEL);
        self.verify_with_given_transcript(
            asset_id,
            balance,
            counter,
            id,
            pk,
            account_commitment,
            nonce,
            account_comm_key,
            transcript,
        )
    }

    pub fn verify_with_given_transcript(
        &self,
        asset_id: AssetId,
        balance: Balance,
        counter: PendingTxnCounter,
        id: G::ScalarField,
        pk: &G,
        account_commitment: AccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        mut transcript: MerlinTranscript,
    ) -> Result<()> {
        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            ID_LABEL,
            id,
            PK_LABEL,
            pk
        );

        let null_gen = account_comm_key.current_rho_gen();
        let pk_gen = account_comm_key.sk_gen();

        self.t_acc.serialize_compressed(&mut transcript)?;
        self.resp_null
            .challenge_contribution(&null_gen, &self.nullifier, &mut transcript)?;
        self.resp_pk
            .challenge_contribution(&pk_gen, &pk, &mut transcript)?;

        let verifier_challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let y = account_commitment.0.into_group()
            - (pk.into_group()
                + account_comm_key.balance_gen() * G::ScalarField::from(balance)
                + account_comm_key.counter_gen() * G::ScalarField::from(counter)
                + account_comm_key.asset_id_gen() * G::ScalarField::from(asset_id)
                + account_comm_key.id_gen() * id);
        self.resp_acc.is_valid(
            &[
                account_comm_key.rho_gen(),
                account_comm_key.current_rho_gen(),
                account_comm_key.randomness_gen(),
                account_comm_key.current_randomness_gen(),
                account_comm_key.sk_enc_gen(),
            ],
            &y.into_affine(),
            &self.t_acc,
            &verifier_challenge,
        )?;

        // rho in account matches the one in nullifier
        if !self.resp_null.verify(
            &self.nullifier,
            &null_gen,
            &verifier_challenge,
            &self.resp_acc.0[1],
        ) {
            return Err(Error::ProofVerificationError(
                "Nullifier proof verification failed".to_string(),
            ));
        }
        if !self.resp_pk.verify(&pk, &pk_gen, &verifier_challenge) {
            return Err(Error::ProofVerificationError(
                "Public key proof verification failed".to_string(),
            ));
        }
        Ok(())
    }
}

/// This is the proof for doing proof of balance with an arbitrary party. Report section 5.1.11, fig 10
/// This reveals the ID for proof efficiency as the public key is already revealed.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PobWithAnyoneProof<G: AffineRepr> {
    pub nullifier: G,
    pub t_acc: G,
    pub resp_acc: SchnorrResponse<G>,
    pub resp_null: PartialPokDiscreteLog<G>,
    pub resp_pk: PokDiscreteLog<G>,
    /// For proving correctness of twisted Elgamal ciphertext of asset-id in each leg: `C_{at} - h * at = S[3] * sk_en^{-1}`
    ///
    /// Structural invariants (enforced by the verifier):
    /// - `resp_asset_id.len() == legs.len()`
    /// - `resp_asset_id[i].is_some()` iff the corresponding leg hides the asset ID
    ///   (i.e., iff `!legs[i].is_asset_id_revealed()`)
    pub resp_asset_id: Vec<Option<PartialPokDiscreteLog<G>>>,
    /// Proving relationship `\sum{C_v} - (\sum{R[2]}) * sk_en^{-1} = h * \sum{v}`
    pub resp_recv_amount: Option<PartialPokDiscreteLog<G>>,
    /// Proving relationship `\sum{C_v} - (\sum{S[2]}) * sk_en^{-1} = h * \sum{v}`
    pub resp_sent_amount: Option<PartialPokDiscreteLog<G>>,
}

impl<G: AffineRepr> PobWithAnyoneProof<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        pk: &G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        // Next few fields args can be abstracted in a single argument. Like a map with key as index and value as legs, keys, etc for that index
        legs: Vec<LegEncryption<G>>,
        sender_in_leg_indices: BTreeSet<usize>,
        receiver_in_leg_indices: BTreeSet<usize>,
        pending_sent_amount: Balance,
        pending_recv_amount: Balance,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        enc_gen: G,
    ) -> Result<Self> {
        let transcript = MerlinTranscript::new(TXN_POB_LABEL);
        Self::new_with_given_transcript(
            rng,
            pk,
            account,
            account_commitment,
            legs,
            sender_in_leg_indices,
            receiver_in_leg_indices,
            pending_sent_amount,
            pending_recv_amount,
            nonce,
            account_comm_key,
            enc_gen,
            transcript,
        )
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        pk: &G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        // Next few fields args can be abstracted in a single argument. Like a map with key as index and value as legs, keys, etc for that index
        legs: Vec<LegEncryption<G>>,
        sender_in_leg_indices: BTreeSet<usize>,
        receiver_in_leg_indices: BTreeSet<usize>,
        pending_sent_amount: Balance,
        pending_recv_amount: Balance,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        enc_gen: G,
        mut transcript: MerlinTranscript,
    ) -> Result<Self> {
        if legs.len() != (sender_in_leg_indices.len() + receiver_in_leg_indices.len()) {
            return Err(Error::ProofGenerationError(
                "Number of legs and indices for sender and receiver do not match".to_string(),
            ));
        }

        for leg in &legs {
            if let Some(revealed_asset_id) = leg.asset_id() {
                if revealed_asset_id != account.asset_id {
                    return Err(Error::ProofGenerationError(format!(
                        "Asset-id mismatch: leg reveals {}, but account has {}",
                        revealed_asset_id, account.asset_id
                    )));
                }
            }
        }

        let num_pending_txns = legs.len();
        // Need to prove that:
        // 1. sk used in commitment is for the revealed pk
        // 2. counter equals number of leg encryptions
        // 3. pk has the respective role in each leg
        // 4. asset-id is the given one in all legs
        // 5. sum of amounts in pending send txns equals the given public value
        // 6. sum of amounts in pending receive txns equals the given public value
        // 7. nullifier is created from current_rho of account commitment

        // The prover should share the index of account commitment in tree so verifier can efficiently fetch the commitment and compare.
        // If its not possible then do a membership proof. Prover could hide the commitment by randomizing it with a new blinding (C' = C + B.r')

        // `S` and `R` are the ephemeral publics of sender and receiver in the leg
        // Since asset-id is revealed, for all legs prove `C_{at} - h * at = S[3] * sk_en^{-1}`, here `at` is revealed to the verifier so only 1 witness.
        // Dont need to prove anything about `C_{s, i}, C_{r, i}` since correctness of `S` and `C` had been proved during leg creation
        // For amount relation, `\sum{C_v} - \sum{S[2]} * sk_en^{-1} = h * \sum{v}`
        // For all above i have assumed prover is sender but for receiver, replace `S` with `R`.

        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            PENDING_SENT_AMOUNT_LABEL,
            pending_sent_amount,
            PENDING_RECV_AMOUNT_LABEL,
            pending_recv_amount,
            ASSET_ID_LABEL,
            account.asset_id,
            BALANCE_LABEL,
            account.balance,
            COUNTER_LABEL,
            account.counter,
            ID_LABEL,
            account.id,
            PK_LABEL,
            pk
        );

        // Add legs separately since it's an array
        for l in &legs {
            transcript.append(LEGS_LABEL, l);
        }

        let nullifier = account.nullifier(&account_comm_key);

        let sk_blinding = G::ScalarField::rand(rng);
        let sk_enc_inv_blinding = G::ScalarField::rand(rng);
        let current_rho_blinding = G::ScalarField::rand(rng);

        let t_acc = SchnorrCommitment::new(
            &[
                account_comm_key.rho_gen(),
                account_comm_key.current_rho_gen(),
                account_comm_key.randomness_gen(),
                account_comm_key.current_randomness_gen(),
                account_comm_key.sk_enc_gen(),
            ],
            vec![
                G::ScalarField::rand(rng),
                current_rho_blinding,
                G::ScalarField::rand(rng),
                G::ScalarField::rand(rng),
                sk_enc_inv_blinding,
            ],
        );
        let t_null = PokDiscreteLogProtocol::init(
            account.current_rho,
            current_rho_blinding,
            &account_comm_key.current_rho_gen(),
        );
        // To prove secret key in account state is same as in public key
        let t_pk =
            PokDiscreteLogProtocol::init(account.sk, sk_blinding, &account_comm_key.sk_gen());

        // For proving correctness of twisted Elgamal ciphertext of asset-id in each leg: `C_{at} - h * at = S[3] * sk_en^{-1}`
        let mut t_asset_id = Vec::with_capacity(num_pending_txns);
        let mut eph_pk_bases_for_asset_id = Vec::with_capacity(num_pending_txns);

        // Sum of all C_v where prover is sender
        let mut enc_total_send = G::Group::zero();
        let mut eph_pk_amount_total_send = G::Group::zero();
        // Sum of all C_v where prover is receiver
        let mut enc_total_recv = G::Group::zero();
        let mut eph_pk_amount_total_recv = G::Group::zero();

        for i in 0..num_pending_txns {
            if receiver_in_leg_indices.contains(&i) {
                eph_pk_amount_total_recv += legs[i].eph_pk_r.2.into_group();
                enc_total_recv += legs[i].ct_amount;
                eph_pk_bases_for_asset_id.push(legs[i].eph_pk_r.3.clone());
            } else if sender_in_leg_indices.contains(&i) {
                eph_pk_amount_total_send += legs[i].eph_pk_s.2.into_group();
                enc_total_send += legs[i].ct_amount;
                eph_pk_bases_for_asset_id.push(legs[i].eph_pk_s.3.clone());
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }

            t_asset_id.push((!legs[i].is_asset_id_revealed()).then(|| {
                PokDiscreteLogProtocol::init(
                    account.sk_enc_inv,
                    sk_enc_inv_blinding,
                    eph_pk_bases_for_asset_id[i].as_ref().unwrap(),
                )
            }));
        }

        let eph_pk_amount_total_send = eph_pk_amount_total_send.into_affine();
        let eph_pk_amount_total_recv = eph_pk_amount_total_recv.into_affine();

        // Proving knowledge of sk_en^{-1} in \sum{C_v} - h * \sum{v} = \sum{S[2]} * sk_en^{-1} where prover is sender. \sum{v} is the total sent amount in the legs
        let t_sent_amount = (!sender_in_leg_indices.is_empty()).then(|| {
            PokDiscreteLogProtocol::init(
                account.sk_enc_inv,
                sk_enc_inv_blinding,
                &eph_pk_amount_total_send,
            )
        });
        // Proving knowledge of sk_en^{-1} in \sum{C_v} - h * \sum{v} = \sum{R[2]} * sk_en^{-1} where prover is receiver. \sum{v} is the total received amount in the legs
        let t_recv_amount = (!receiver_in_leg_indices.is_empty()).then(|| {
            PokDiscreteLogProtocol::init(
                account.sk_enc_inv,
                sk_enc_inv_blinding,
                &eph_pk_amount_total_recv,
            )
        });

        t_acc.challenge_contribution(&mut transcript)?;
        t_null.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &nullifier,
            &mut transcript,
        )?;
        t_pk.challenge_contribution(&account_comm_key.sk_gen(), &pk, &mut transcript)?;

        let minus_h_at = enc_gen.into_group().neg() * G::ScalarField::from(account.asset_id);
        for i in 0..num_pending_txns {
            if let Some(t) = &t_asset_id[i] {
                let y = (legs[i].asset_id_ciphertext().unwrap().into_group() + minus_h_at)
                    .into_affine();
                t.challenge_contribution(
                    eph_pk_bases_for_asset_id[i].as_ref().unwrap(),
                    &y,
                    &mut transcript,
                )?;
            }
        }

        if let Some(t) = &t_sent_amount {
            let y = enc_total_send - (enc_gen * G::ScalarField::from(pending_sent_amount));
            t.challenge_contribution(&eph_pk_amount_total_send, &y.into_affine(), &mut transcript)?;
        }
        if let Some(t) = &t_recv_amount {
            let y = enc_total_recv - (enc_gen * G::ScalarField::from(pending_recv_amount));
            t.challenge_contribution(&eph_pk_amount_total_recv, &y.into_affine(), &mut transcript)?;
        }

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let resp_acc = t_acc.response(
            &[
                account.rho,
                account.current_rho,
                account.randomness,
                account.current_randomness,
                account.sk_enc_inv,
            ],
            &challenge,
        )?;

        // Response for witness will already be generated in sigma protocol for account commitment
        let resp_null = t_null.gen_partial_proof();

        let resp_pk = t_pk.gen_proof(&challenge);

        let mut resp_asset_id = Vec::with_capacity(num_pending_txns);
        for t in t_asset_id.into_iter() {
            resp_asset_id.push(t.map(|t| t.gen_partial_proof()));
        }

        let resp_sent_amount = t_sent_amount.map(|t| t.gen_partial_proof());
        let resp_recv_amount = t_recv_amount.map(|t| t.gen_partial_proof());

        Ok(Self {
            nullifier,
            t_acc: t_acc.t,
            resp_acc,
            resp_null,
            resp_pk,
            resp_asset_id,
            resp_recv_amount,
            resp_sent_amount,
        })
    }

    pub fn verify(
        &self,
        asset_id: AssetId,
        balance: Balance,
        counter: PendingTxnCounter,
        id: G::ScalarField,
        pk: &G,
        account_commitment: AccountStateCommitment<G>,
        legs: Vec<LegEncryption<G>>,
        sender_in_leg_indices: BTreeSet<usize>,
        receiver_in_leg_indices: BTreeSet<usize>,
        pending_sent_amount: Balance,
        pending_recv_amount: Balance,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        enc_gen: G,
    ) -> Result<()> {
        let transcript = MerlinTranscript::new(TXN_POB_LABEL);
        self.verify_with_given_transcript(
            asset_id,
            balance,
            counter,
            id,
            pk,
            account_commitment,
            legs,
            sender_in_leg_indices,
            receiver_in_leg_indices,
            pending_sent_amount,
            pending_recv_amount,
            nonce,
            account_comm_key,
            enc_gen,
            transcript,
        )
    }

    pub fn verify_with_given_transcript(
        &self,
        asset_id: AssetId,
        balance: Balance,
        counter: PendingTxnCounter,
        id: G::ScalarField,
        pk: &G,
        account_commitment: AccountStateCommitment<G>,
        legs: Vec<LegEncryption<G>>,
        sender_in_leg_indices: BTreeSet<usize>,
        receiver_in_leg_indices: BTreeSet<usize>,
        pending_sent_amount: Balance,
        pending_recv_amount: Balance,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        enc_gen: G,
        mut transcript: MerlinTranscript,
    ) -> Result<()> {
        if legs.len() != counter as usize {
            return Err(Error::ProofVerificationError(
                "Number of legs and counter do not match".to_string(),
            ));
        }
        if legs.len() != (sender_in_leg_indices.len() + receiver_in_leg_indices.len()) {
            return Err(Error::ProofVerificationError(
                "Number of legs and indices for sender and receiver do not match".to_string(),
            ));
        }

        if self.resp_asset_id.len() != legs.len() {
            return Err(Error::ProofVerificationError(format!(
                "resp_asset_id length mismatch: expected {}, got {}",
                legs.len(),
                self.resp_asset_id.len()
            )));
        }

        if sender_in_leg_indices.len() > 0 {
            if self.resp_sent_amount.is_none() {
                return Err(Error::ProofVerificationError(
                    "No response for sender amount".to_string(),
                ));
            }
        }
        if receiver_in_leg_indices.len() > 0 {
            if self.resp_recv_amount.is_none() {
                return Err(Error::ProofVerificationError(
                    "No response for receiver amount".to_string(),
                ));
            }
        }

        for leg in &legs {
            if let Some(revealed_asset_id) = leg.asset_id() {
                if revealed_asset_id != asset_id {
                    return Err(Error::ProofVerificationError(format!(
                        "Asset-id mismatch: leg reveals {}, but expected {}",
                        revealed_asset_id, asset_id
                    )));
                }
            }
        }

        let num_pending_txns = legs.len();

        let at = G::ScalarField::from(asset_id);
        let minus_h_at = enc_gen.into_group().neg() * at;

        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            PENDING_SENT_AMOUNT_LABEL,
            pending_sent_amount,
            PENDING_RECV_AMOUNT_LABEL,
            pending_recv_amount,
            ASSET_ID_LABEL,
            asset_id,
            BALANCE_LABEL,
            balance,
            COUNTER_LABEL,
            counter,
            ID_LABEL,
            id,
            PK_LABEL,
            pk
        );

        // Add legs separately since it's an array
        for l in &legs {
            transcript.append(LEGS_LABEL, l);
        }

        self.t_acc.serialize_compressed(&mut transcript)?;
        self.resp_null.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &self.nullifier,
            &mut transcript,
        )?;
        self.resp_pk
            .challenge_contribution(&account_comm_key.sk_gen(), pk, &mut transcript)?;

        let mut enc_total_send = G::Group::zero();
        let mut enc_total_recv = G::Group::zero();
        let mut eph_pk_amount_total_send = G::Group::zero();
        let mut eph_pk_amount_total_recv = G::Group::zero();
        let mut eph_pk_bases_for_asset_id = Vec::with_capacity(legs.len());
        let mut y_asset_id = Vec::with_capacity(legs.len());
        for i in 0..num_pending_txns {
            if receiver_in_leg_indices.contains(&i) {
                enc_total_recv += legs[i].ct_amount;
                eph_pk_amount_total_recv += legs[i].eph_pk_r.2.into_group();
                eph_pk_bases_for_asset_id.push(legs[i].eph_pk_r.3.clone());
            } else if sender_in_leg_indices.contains(&i) {
                enc_total_send += legs[i].ct_amount;
                eph_pk_amount_total_send += legs[i].eph_pk_s.2.into_group();
                eph_pk_bases_for_asset_id.push(legs[i].eph_pk_s.3.clone());
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }

            let y = legs[i]
                .asset_id_ciphertext()
                .map(|ct| (ct.into_group() + minus_h_at).into_affine());
            y_asset_id.push(y);

            let expects_asset_id_proof = !legs[i].is_asset_id_revealed();
            let has_resp = self.resp_asset_id[i].is_some();
            if expects_asset_id_proof != has_resp {
                return Err(Error::ProofVerificationError(format!(
                    "resp_asset_id presence mismatch at leg {}: expected {}, got {}",
                    i, expects_asset_id_proof, has_resp
                )));
            }
            if expects_asset_id_proof {
                if eph_pk_bases_for_asset_id[i].is_none() {
                    return Err(Error::ProofVerificationError(format!(
                        "Missing asset-id ephemeral key for hidden-asset leg {}",
                        i
                    )));
                }
                if y_asset_id[i].is_none() {
                    return Err(Error::ProofVerificationError(format!(
                        "Missing asset-id ciphertext for hidden-asset leg {}",
                        i
                    )));
                }
            }
        }

        for i in 0..num_pending_txns {
            if legs[i].is_asset_id_revealed() {
                continue;
            }
            let resp = self
                .resp_asset_id
                .get(i)
                .and_then(|r| r.as_ref())
                .ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Missing resp_asset_id for hidden-asset leg {}",
                        i
                    ))
                })?;
            let base = eph_pk_bases_for_asset_id[i].as_ref().ok_or_else(|| {
                Error::ProofVerificationError(format!(
                    "Missing asset-id ephemeral key for hidden-asset leg {}",
                    i
                ))
            })?;
            let y = y_asset_id[i].as_ref().ok_or_else(|| {
                Error::ProofVerificationError(format!(
                    "Missing asset-id ciphertext relation input for hidden-asset leg {}",
                    i
                ))
            })?;
            resp.challenge_contribution(base, y, &mut transcript)?;
        }

        let y_total_send = if let Some(resp) = &self.resp_sent_amount {
            let y_total_send = (enc_total_send
                - (enc_gen * G::ScalarField::from(pending_sent_amount)))
            .into_affine();
            resp.challenge_contribution(
                &eph_pk_amount_total_send.into_affine(),
                &y_total_send,
                &mut transcript,
            )?;
            Some(y_total_send)
        } else {
            None
        };

        let y_total_recv = if let Some(resp) = &self.resp_recv_amount {
            let y_total_recv = (enc_total_recv
                - (enc_gen * G::ScalarField::from(pending_recv_amount)))
            .into_affine();
            resp.challenge_contribution(
                &eph_pk_amount_total_recv.into_affine(),
                &y_total_recv,
                &mut transcript,
            )?;
            Some(y_total_recv)
        } else {
            None
        };

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let y = account_commitment.0.into_group()
            - (pk.into_group()
                + account_comm_key.balance_gen() * G::ScalarField::from(balance)
                + account_comm_key.counter_gen() * G::ScalarField::from(counter)
                + account_comm_key.asset_id_gen() * G::ScalarField::from(asset_id)
                + account_comm_key.id_gen() * id);
        self.resp_acc.is_valid(
            &[
                account_comm_key.rho_gen(),
                account_comm_key.current_rho_gen(),
                account_comm_key.randomness_gen(),
                account_comm_key.current_randomness_gen(),
                account_comm_key.sk_enc_gen(),
            ],
            &y.into_affine(),
            &self.t_acc,
            &challenge,
        )?;

        // rho in account matches the one in nullifier
        if !self.resp_null.verify(
            &self.nullifier,
            &account_comm_key.current_rho_gen(),
            &challenge,
            &self.resp_acc.0[1],
        ) {
            return Err(Error::ProofVerificationError(
                "Nullifier verification failed".to_string(),
            ));
        }

        if !self
            .resp_pk
            .verify(&pk, &account_comm_key.sk_gen(), &challenge)
        {
            return Err(Error::ProofVerificationError(
                "Public key verification failed".to_string(),
            ));
        }

        let resp_sk_enc_inv = &self.resp_acc.0[4];
        for i in 0..num_pending_txns {
            if legs[i].is_asset_id_revealed() {
                continue;
            }
            let resp = self
                .resp_asset_id
                .get(i)
                .and_then(|r| r.as_ref())
                .ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Missing resp_asset_id for hidden-asset leg {}",
                        i
                    ))
                })?;
            let base = eph_pk_bases_for_asset_id[i].as_ref().ok_or_else(|| {
                Error::ProofVerificationError(format!(
                    "Missing asset-id ephemeral key for hidden-asset leg {}",
                    i
                ))
            })?;
            let y = y_asset_id[i].as_ref().ok_or_else(|| {
                Error::ProofVerificationError(format!(
                    "Missing asset-id ciphertext relation input for hidden-asset leg {}",
                    i
                ))
            })?;
            if !resp.verify(y, base, &challenge, resp_sk_enc_inv) {
                return Err(Error::ProofVerificationError(
                    "Asset-id verification failed".to_string(),
                ));
            }
        }

        if let Some(resp) = &self.resp_sent_amount {
            if !resp.verify(
                &y_total_send.unwrap(),
                &eph_pk_amount_total_send.into_affine(),
                &challenge,
                resp_sk_enc_inv,
            ) {
                return Err(Error::ProofVerificationError(
                    "resp_sent_amount verification failed".to_string(),
                ));
            }
        }

        if let Some(resp) = &self.resp_recv_amount {
            if !resp.verify(
                &y_total_recv.unwrap(),
                &eph_pk_amount_total_recv.into_affine(),
                &challenge,
                resp_sk_enc_inv,
            ) {
                return Err(Error::ProofVerificationError(
                    "resp_recv_amount verification failed".to_string(),
                ));
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::account_registration::tests::{new_account, setup_comm_key};
    use crate::keys::{keygen_enc, keygen_sig};
    use crate::leg::tests::setup_keys;
    use crate::leg::{Leg, LegEncConfig};
    use std::time::Instant;

    type PallasA = ark_pallas::Affine;
    type PallasFr = ark_pallas::Fr;

    #[test]
    fn pob_with_auditor_as_verifier() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key(b"testing");

        let asset_id = 1;

        let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let enc_key_gen = account_comm_key.sk_enc_gen();
        let (sk_enc, _) = keygen_enc(&mut rng, enc_key_gen);
        // Account exists with some balance and pending txns
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk, sk_enc, id.clone());
        account.balance = 1000;
        account.counter = 7;
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let nonce = b"test-nonce";

        let proof = PobWithAuditorProof::new(
            &mut rng,
            &pk.0,
            &account,
            account_comm.clone(),
            nonce,
            account_comm_key.clone(),
        )
        .unwrap();

        proof
            .verify(
                asset_id,
                account.balance,
                account.counter,
                id,
                &pk.0,
                account_comm,
                nonce,
                account_comm_key,
            )
            .unwrap();
    }

    #[test]
    fn pob_with_anyone() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key(b"testing");

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let enc_gen = PallasA::rand(&mut rng);

        let (((sk, pk), (sk_e, pk_e)), (_, (_, pk_e_other)), ((_, _), (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let num_pending_txns = 20;

        // Account exists with some balance and pending txns
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk, sk_e, id.clone());
        account.balance = 1000000;
        account.counter = num_pending_txns;
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        // Create some legs as pending transfers
        let mut legs = vec![];
        // Set this amount in each leg. Just for testing, in practice it could be different
        let amount = 10u64;
        let mut pending_sent_amount = 0u64;
        let mut pending_recv_amount = 0u64;
        let mut sender_in_leg_indices = BTreeSet::new();
        let mut receiver_in_leg_indices = BTreeSet::new();
        for i in 0..num_pending_txns as usize {
            // for odd i, account is sender, for even i, its receiver
            let leg_enc = if i % 2 == 0 {
                pending_recv_amount += amount;
                receiver_in_leg_indices.insert(i);
                let leg = Leg::new(
                    pk_e_other.0,
                    pk_e.0,
                    amount,
                    asset_id,
                    vec![pk_a_e.0],
                    vec![],
                    vec![],
                )
                .unwrap();
                let (leg_enc, _) = leg
                    .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
                    .unwrap();
                leg_enc
            } else {
                pending_sent_amount += amount;
                sender_in_leg_indices.insert(i);
                let leg = Leg::new(
                    pk_e.0,
                    pk_e_other.0,
                    amount,
                    asset_id,
                    vec![pk_a_e.0],
                    vec![],
                    vec![],
                )
                .unwrap();
                let (leg_enc, _) = leg
                    .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
                    .unwrap();
                leg_enc
            };
            legs.push(leg_enc);
        }

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let proof = PobWithAnyoneProof::new(
            &mut rng,
            &pk.0,
            &account,
            account_comm.clone(),
            legs.clone(),
            sender_in_leg_indices.clone(),
            receiver_in_leg_indices.clone(),
            pending_sent_amount,
            pending_recv_amount,
            nonce,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                asset_id,
                account.balance,
                account.counter,
                id,
                &pk.0,
                account_comm,
                legs,
                sender_in_leg_indices.clone(),
                receiver_in_leg_indices.clone(),
                pending_sent_amount,
                pending_recv_amount,
                nonce,
                account_comm_key,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        log::info!("For {num_pending_txns} pending txns");
        log::info!("total proof size = {}", proof.compressed_size());
        log::info!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time,
            verifier_time
        );
    }

    #[test]
    fn pob_with_anyone_revealed_asset_id() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key(b"testing");

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let enc_gen = PallasA::rand(&mut rng);

        let (((sk, pk), (sk_e, pk_e)), ((_, _), (_, pk_e_other)), ((_, _), (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let num_pending_txns = 20;

        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk, sk_e, id.clone());
        account.balance = 1000000;
        account.counter = num_pending_txns;
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let mut legs = vec![];
        let amount = 10u64;
        let mut pending_sent_amount = 0u64;
        let mut pending_recv_amount = 0u64;
        let mut sender_in_leg_indices = BTreeSet::new();
        let mut receiver_in_leg_indices = BTreeSet::new();
        for i in 0..num_pending_txns as usize {
            let leg_enc = if i % 2 == 0 {
                pending_recv_amount += amount;
                receiver_in_leg_indices.insert(i);
                let leg = Leg::new(
                    pk_e_other.0,
                    pk_e.0,
                    amount,
                    asset_id,
                    vec![pk_a_e.0],
                    vec![],
                    vec![],
                )
                .unwrap();
                let config = if i % 4 == 0 {
                    LegEncConfig {
                        parties_see_each_other: true,
                        reveal_asset_id: true,
                    }
                } else {
                    LegEncConfig::default()
                };
                let (leg_enc, _) = leg.encrypt(&mut rng, config, enc_key_gen, enc_gen).unwrap();
                leg_enc
            } else {
                pending_sent_amount += amount;
                sender_in_leg_indices.insert(i);
                let leg = Leg::new(
                    pk_e.0,
                    pk_e_other.0,
                    amount,
                    asset_id,
                    vec![pk_a_e.0],
                    vec![],
                    vec![],
                )
                .unwrap();
                let config = if i % 4 == 1 {
                    LegEncConfig {
                        parties_see_each_other: true,
                        reveal_asset_id: true,
                    }
                } else {
                    LegEncConfig::default()
                };
                let (leg_enc, _) = leg.encrypt(&mut rng, config, enc_key_gen, enc_gen).unwrap();
                leg_enc
            };
            legs.push(leg_enc);
        }

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let proof = PobWithAnyoneProof::new(
            &mut rng,
            &pk.0,
            &account,
            account_comm.clone(),
            legs.clone(),
            sender_in_leg_indices.clone(),
            receiver_in_leg_indices.clone(),
            pending_sent_amount,
            pending_recv_amount,
            nonce,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                asset_id,
                account.balance,
                account.counter,
                id,
                &pk.0,
                account_comm,
                legs,
                sender_in_leg_indices.clone(),
                receiver_in_leg_indices.clone(),
                pending_sent_amount,
                pending_recv_amount,
                nonce,
                account_comm_key,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("For {num_pending_txns} pending txns");
        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );
    }

    #[test]
    fn pob_with_anyone_missing_resp_asset_id_on_hidden_leg_fails() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key(b"testing");

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let enc_gen = PallasA::rand(&mut rng);

        let (((sk, pk), (sk_e, pk_e)), (_, (_, pk_e_other)), ((_, _), (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let num_pending_txns = 10;

        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk, sk_e, id);
        account.balance = 1000000;
        account.counter = num_pending_txns;
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let mut legs = vec![];
        let amount = 10u64;
        let mut pending_sent_amount = 0u64;
        let mut pending_recv_amount = 0u64;
        let mut sender_in_leg_indices = BTreeSet::new();
        let mut receiver_in_leg_indices = BTreeSet::new();
        for i in 0..num_pending_txns as usize {
            let leg_enc = if i % 2 == 0 {
                pending_recv_amount += amount;
                receiver_in_leg_indices.insert(i);
                let leg = Leg::new(
                    pk_e_other.0,
                    pk_e.0,
                    amount,
                    asset_id,
                    vec![pk_a_e.0],
                    vec![],
                    vec![],
                )
                .unwrap();
                let (leg_enc, _) = leg
                    .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
                    .unwrap();
                leg_enc
            } else {
                pending_sent_amount += amount;
                sender_in_leg_indices.insert(i);
                let leg = Leg::new(
                    pk_e.0,
                    pk_e_other.0,
                    amount,
                    asset_id,
                    vec![pk_a_e.0],
                    vec![],
                    vec![],
                )
                .unwrap();
                let (leg_enc, _) = leg
                    .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
                    .unwrap();
                leg_enc
            };
            legs.push(leg_enc);
        }

        let nonce = b"test-nonce";

        let mut proof = PobWithAnyoneProof::new(
            &mut rng,
            &pk.0,
            &account,
            account_comm.clone(),
            legs.clone(),
            sender_in_leg_indices.clone(),
            receiver_in_leg_indices.clone(),
            pending_sent_amount,
            pending_recv_amount,
            nonce,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        // All legs are hidden-asset-id with default config; dropping one response should fail.
        proof.resp_asset_id[0] = None;

        assert!(
            proof
                .verify(
                    asset_id,
                    account.balance,
                    account.counter,
                    account.id,
                    &pk.0,
                    account_comm,
                    legs,
                    sender_in_leg_indices,
                    receiver_in_leg_indices,
                    pending_sent_amount,
                    pending_recv_amount,
                    nonce,
                    account_comm_key,
                    enc_gen,
                )
                .is_err()
        );
    }

    #[test]
    fn pob_with_anyone_extra_resp_asset_id_on_revealed_leg_fails() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key(b"testing");

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let enc_gen = PallasA::rand(&mut rng);

        let (((sk, pk), (sk_e, pk_e)), ((_, _), (_, pk_e_other)), ((_, _), (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let num_pending_txns = 12;

        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk, sk_e, id);
        account.balance = 1000000;
        account.counter = num_pending_txns;
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let mut legs = vec![];
        let amount = 10u64;
        let mut pending_sent_amount = 0u64;
        let mut pending_recv_amount = 0u64;
        let mut sender_in_leg_indices = BTreeSet::new();
        let mut receiver_in_leg_indices = BTreeSet::new();
        for i in 0..num_pending_txns as usize {
            let leg_enc = if i % 2 == 0 {
                pending_recv_amount += amount;
                receiver_in_leg_indices.insert(i);
                let leg = Leg::new(
                    pk_e_other.0,
                    pk_e.0,
                    amount,
                    asset_id,
                    vec![pk_a_e.0],
                    vec![],
                    vec![],
                )
                .unwrap();
                let config = if i % 4 == 0 {
                    LegEncConfig {
                        parties_see_each_other: true,
                        reveal_asset_id: true,
                    }
                } else {
                    LegEncConfig::default()
                };
                let (leg_enc, _) = leg.encrypt(&mut rng, config, enc_key_gen, enc_gen).unwrap();
                leg_enc
            } else {
                pending_sent_amount += amount;
                sender_in_leg_indices.insert(i);
                let leg = Leg::new(
                    pk_e.0,
                    pk_e_other.0,
                    amount,
                    asset_id,
                    vec![pk_a_e.0],
                    vec![],
                    vec![],
                )
                .unwrap();
                let config = if i % 4 == 1 {
                    LegEncConfig {
                        parties_see_each_other: true,
                        reveal_asset_id: true,
                    }
                } else {
                    LegEncConfig::default()
                };
                let (leg_enc, _) = leg.encrypt(&mut rng, config, enc_key_gen, enc_gen).unwrap();
                leg_enc
            };
            legs.push(leg_enc);
        }

        let nonce = b"test-nonce";

        let mut proof = PobWithAnyoneProof::new(
            &mut rng,
            &pk.0,
            &account,
            account_comm.clone(),
            legs.clone(),
            sender_in_leg_indices.clone(),
            receiver_in_leg_indices.clone(),
            pending_sent_amount,
            pending_recv_amount,
            nonce,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        // Find one revealed leg and one hidden leg response; copy hidden response into revealed slot.
        let revealed_idx = legs
            .iter()
            .position(|l| l.is_asset_id_revealed())
            .expect("test requires at least one revealed leg");
        let hidden_idx = legs
            .iter()
            .position(|l| !l.is_asset_id_revealed())
            .expect("test requires at least one hidden leg");
        let hidden_resp = proof.resp_asset_id[hidden_idx]
            .as_ref()
            .expect("hidden leg should have asset-id response")
            .clone();
        proof.resp_asset_id[revealed_idx] = Some(hidden_resp);

        assert!(
            proof
                .verify(
                    asset_id,
                    account.balance,
                    account.counter,
                    account.id,
                    &pk.0,
                    account_comm,
                    legs,
                    sender_in_leg_indices,
                    receiver_in_leg_indices,
                    pending_sent_amount,
                    pending_recv_amount,
                    nonce,
                    account_comm_key,
                    enc_gen,
                )
                .is_err()
        );
    }

    #[test]
    fn pob_with_anyone_resp_asset_id_len_mismatch_fails() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key(b"testing");

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let enc_gen = PallasA::rand(&mut rng);

        let (((sk, pk), (sk_e, pk_e)), (_, (_, pk_e_other)), ((_, _), (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let num_pending_txns = 6;

        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk, sk_e, id);
        account.balance = 1000000;
        account.counter = num_pending_txns;
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let mut legs = vec![];
        let amount = 10u64;
        let mut pending_sent_amount = 0u64;
        let mut pending_recv_amount = 0u64;
        let mut sender_in_leg_indices = BTreeSet::new();
        let mut receiver_in_leg_indices = BTreeSet::new();
        for i in 0..num_pending_txns as usize {
            let leg_enc = if i % 2 == 0 {
                pending_recv_amount += amount;
                receiver_in_leg_indices.insert(i);
                let leg = Leg::new(
                    pk_e_other.0,
                    pk_e.0,
                    amount,
                    asset_id,
                    vec![pk_a_e.0],
                    vec![],
                    vec![],
                )
                .unwrap();
                let (leg_enc, _) = leg
                    .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
                    .unwrap();
                leg_enc
            } else {
                pending_sent_amount += amount;
                sender_in_leg_indices.insert(i);
                let leg = Leg::new(
                    pk_e.0,
                    pk_e_other.0,
                    amount,
                    asset_id,
                    vec![pk_a_e.0],
                    vec![],
                    vec![],
                )
                .unwrap();
                let (leg_enc, _) = leg
                    .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
                    .unwrap();
                leg_enc
            };
            legs.push(leg_enc);
        }

        let nonce = b"test-nonce";

        let mut proof = PobWithAnyoneProof::new(
            &mut rng,
            &pk.0,
            &account,
            account_comm.clone(),
            legs.clone(),
            sender_in_leg_indices.clone(),
            receiver_in_leg_indices.clone(),
            pending_sent_amount,
            pending_recv_amount,
            nonce,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        proof.resp_asset_id.pop();

        assert!(
            proof
                .verify(
                    asset_id,
                    account.balance,
                    account.counter,
                    account.id,
                    &pk.0,
                    account_comm,
                    legs,
                    sender_in_leg_indices,
                    receiver_in_leg_indices,
                    pending_sent_amount,
                    pending_recv_amount,
                    nonce,
                    account_comm_key,
                    enc_gen,
                )
                .is_err()
        );
    }
}
