use crate::account::{
    AccountCommitmentKeyTrait, AccountState, AccountStateCommitment, COUNTER_LABEL, LEGS_LABEL,
};
use crate::leg::{LegEncryption, LegEncryptionRandomness};
use crate::{
    ACCOUNT_COMMITMENT_LABEL, ASSET_ID_LABEL, BALANCE_LABEL, Error, ID_LABEL, NONCE_LABEL,
    PK_LABEL, TXN_CHALLENGE_LABEL, add_to_transcript, error,
};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{One, Zero};
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
    ) -> error::Result<Self> {
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
    ) -> error::Result<Self> {
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

        // For proving relation g_i * rho + g_j * current_rho + g_k * randomness = C - (pk + g_a * v + g_b * at + g_c * cnt + g_d * id)
        // where C is the account commitment and rho, current_rho and randomness are the witness, rest are instance
        let t_acc = SchnorrCommitment::new(
            &[
                account_comm_key.rho_gen(),
                null_gen,
                account_comm_key.randomness_gen(),
            ],
            vec![
                G::ScalarField::rand(rng),
                current_rho_blinding,
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
            &[account.rho, account.current_rho, account.randomness],
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
    ) -> error::Result<()> {
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
    ) -> error::Result<()> {
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
    /// For proving correctness of twisted Elgamal ciphertext of asset-id in each leg
    pub asset_id: (G, G::ScalarField),
    /// For proving correctness of twisted Elgamal ciphertext of sender public key. None when prover is sender in no leg.
    pub pk_send: Option<(G, G::ScalarField)>,
    /// For proving correctness of twisted Elgamal ciphertext of receiver public key. None when prover is receiver in no leg.
    pub pk_recv: Option<(G, G::ScalarField)>,
    /// Proving knowledge of `\sum{r_3}` in `\sum{C_v} - h * \sum{v} = g * \sum{r_3}` where prover is receiver. `\sum{v}` is the total received amount in the legs
    pub resp_recv_amount: Option<PokDiscreteLog<G>>,
    /// Proving knowledge of `\sum{r_3}` in `\sum{C_v} - h * \sum{v} = g * \sum{r_3}` where prover is sender. `\sum{v}` is the total sent amount in the legs
    pub resp_sent_amount: Option<PokDiscreteLog<G>>,
}

impl<G: AffineRepr> PobWithAnyoneProof<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        pk: &G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        // Next few fields args can be abstracted in a single argument. Like a map with key as index and value as legs, keys, etc for that index
        legs: Vec<(LegEncryption<G>, LegEncryptionRandomness<G::ScalarField>)>,
        sender_in_leg_indices: BTreeSet<usize>,
        receiver_in_leg_indices: BTreeSet<usize>,
        pending_sent_amount: Balance,
        pending_recv_amount: Balance,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        enc_key_gen: G,
        enc_gen: G,
    ) -> error::Result<Self> {
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
            enc_key_gen,
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
        legs: Vec<(LegEncryption<G>, LegEncryptionRandomness<G::ScalarField>)>,
        sender_in_leg_indices: BTreeSet<usize>,
        receiver_in_leg_indices: BTreeSet<usize>,
        pending_sent_amount: Balance,
        pending_recv_amount: Balance,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        enc_key_gen: G,
        enc_gen: G,
        mut transcript: MerlinTranscript,
    ) -> error::Result<Self> {
        if legs.len() != (sender_in_leg_indices.len() + receiver_in_leg_indices.len()) {
            return Err(Error::ProofGenerationError(
                "Number of legs and indices for sender and receiver do not match".to_string(),
            ));
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

        // Prover has to prove relations of this form for each leg:
        // For sender leg: C_{s, 1} - pk = g * r_{1, i}
        // For receiver leg: C_{r, 1} - pk = g * r_{2, i}
        // For asset-id: C_{at} - h * at = g * r_{4, i}
        // Naively proving, this would lead to 3*n relations for n legs but if we use the batch Schnorr protocol
        // for each of the above 3 relations, we end up with just 3 relations irrespective of number of legs.

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
            transcript.append(LEGS_LABEL, &l.0);
        }

        let nullifier = account.nullifier(&account_comm_key);

        let sk_blinding = G::ScalarField::rand(rng);
        let current_rho_blinding = G::ScalarField::rand(rng);
        let r_1_blinding = (!sender_in_leg_indices.is_empty()).then(|| G::ScalarField::rand(rng));
        let r_2_blinding = (!receiver_in_leg_indices.is_empty()).then(|| G::ScalarField::rand(rng));
        let r_4_blinding = G::ScalarField::rand(rng);

        // Sum of all r_3 where prover is sender
        let mut sum_r_3_sent = G::ScalarField::zero();
        // Sum of all r_3 where prover is receiver
        let mut sum_r_3_recv = G::ScalarField::zero();

        let t_acc = SchnorrCommitment::new(
            &[
                account_comm_key.rho_gen(),
                account_comm_key.current_rho_gen(),
                account_comm_key.randomness_gen(),
            ],
            vec![
                G::ScalarField::rand(rng),
                current_rho_blinding,
                G::ScalarField::rand(rng),
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

        // For proving correctness of twisted Elgamal ciphertext of sender public key. Used when prover is sender in at least 1 leg
        let t_pk_send = r_1_blinding.map(|blinding| (enc_key_gen * blinding).into_affine());
        // For proving correctness of twisted Elgamal ciphertext of receiver public key. Used when prover is receiver in at least 1 leg
        let t_pk_recv = r_2_blinding.map(|blinding| (enc_key_gen * blinding).into_affine());

        // For proving correctness of twisted Elgamal ciphertext of asset-id
        let t_asset_id = (enc_key_gen * r_4_blinding).into_affine();

        // Sum of all C_v where prover is sender
        let mut enc_total_send = G::Group::zero();
        // Sum of all C_v where prover is receiver
        let mut enc_total_recv = G::Group::zero();

        for i in 0..num_pending_txns {
            let LegEncryptionRandomness(_, _, r_3, _) = &legs[i].1;

            if receiver_in_leg_indices.contains(&i) {
                sum_r_3_recv += r_3;
                enc_total_recv += legs[i].0.ct_amount;
            } else if sender_in_leg_indices.contains(&i) {
                sum_r_3_sent += r_3;
                enc_total_send += legs[i].0.ct_amount;
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }
        }

        // Proving knowledge of \sum{r_3} in \sum{C_v} - h * \sum{v} = g * \sum{r_3} where prover is sender. \sum{v} is the total sent amount in the legs
        let t_sent_amount = (!sender_in_leg_indices.is_empty()).then(|| {
            PokDiscreteLogProtocol::init(sum_r_3_sent, G::ScalarField::rand(rng), &enc_key_gen)
        });
        // Proving knowledge of \sum{r_3} in \sum{C_v} - h * \sum{v} = g * \sum{r_3} where prover is receiver. \sum{v} is the total received amount in the legs
        let t_recv_amount = (!receiver_in_leg_indices.is_empty()).then(|| {
            PokDiscreteLogProtocol::init(sum_r_3_recv, G::ScalarField::rand(rng), &enc_key_gen)
        });

        t_acc.challenge_contribution(&mut transcript)?;
        t_null.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &nullifier,
            &mut transcript,
        )?;
        t_pk.challenge_contribution(&account_comm_key.sk_gen(), &pk, &mut transcript)?;

        t_pk_send
            .as_ref()
            .map(|t| transcript.append(b"t_pk_send", t));
        t_pk_recv
            .as_ref()
            .map(|t| transcript.append(b"t_pk_recv", t));
        transcript.append(b"t_asset_id", &t_asset_id);

        if let Some(t) = &t_sent_amount {
            let y = enc_total_send - (enc_gen * G::ScalarField::from(pending_sent_amount));
            t.challenge_contribution(&enc_key_gen, &y.into_affine(), &mut transcript)?;
        }
        if let Some(t) = &t_recv_amount {
            let y = enc_total_recv - (enc_gen * G::ScalarField::from(pending_recv_amount));
            t.challenge_contribution(&enc_key_gen, &y.into_affine(), &mut transcript)?;
        }

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let mut resp_pk_send = r_1_blinding.map(|blinding| blinding);
        let mut resp_pk_recv = r_2_blinding.map(|blinding| blinding);
        let mut resp_asset_id = r_4_blinding;

        let resp_acc = t_acc.response(
            &[account.rho, account.current_rho, account.randomness],
            &challenge,
        )?;

        // Response for witness will already be generated in sigma protocol for account commitment
        let resp_null = t_null.gen_partial_proof();

        let resp_pk = t_pk.gen_proof(&challenge);

        let mut c = challenge;
        for i in 0..num_pending_txns {
            let LegEncryptionRandomness(r_1, r_2, _, r_4) = &legs[i].1;

            if receiver_in_leg_indices.contains(&i) {
                resp_pk_recv = resp_pk_recv.map(|v| v + (c * r_2));
            } else if sender_in_leg_indices.contains(&i) {
                resp_pk_send = resp_pk_send.map(|v| v + (c * r_1));
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }

            resp_asset_id += c * r_4;
            c *= challenge;
        }

        let resp_sent_amount = t_sent_amount.map(|t| t.gen_proof(&challenge));
        let resp_recv_amount = t_recv_amount.map(|t| t.gen_proof(&challenge));

        Ok(Self {
            nullifier,
            t_acc: t_acc.t,
            resp_acc,
            resp_null,
            resp_pk,
            asset_id: (t_asset_id, resp_asset_id),
            pk_recv: t_pk_recv.zip(resp_pk_recv),
            pk_send: t_pk_send.zip(resp_pk_send),
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
        enc_key_gen: G,
        enc_gen: G,
    ) -> error::Result<()> {
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
            enc_key_gen,
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
        enc_key_gen: G,
        enc_gen: G,
        mut transcript: MerlinTranscript,
    ) -> error::Result<()> {
        if legs.len() != counter as usize {
            return Err(Error::ProofGenerationError(
                "Number of legs and counter do not match".to_string(),
            ));
        }
        if legs.len() != (sender_in_leg_indices.len() + receiver_in_leg_indices.len()) {
            return Err(Error::ProofGenerationError(
                "Number of legs and indices for sender and receiver do not match".to_string(),
            ));
        }
        if sender_in_leg_indices.len() > 0 {
            if self.pk_send.is_none() {
                return Err(Error::ProofVerificationError(
                    "No response for sender indices".to_string(),
                ));
            }
            if self.resp_sent_amount.is_none() {
                return Err(Error::ProofVerificationError(
                    "No response for sender amount".to_string(),
                ));
            }
        }
        if receiver_in_leg_indices.len() > 0 {
            if self.pk_recv.is_none() {
                return Err(Error::ProofVerificationError(
                    "No response for receiver indices".to_string(),
                ));
            }
            if self.resp_recv_amount.is_none() {
                return Err(Error::ProofVerificationError(
                    "No response for receiver amount".to_string(),
                ));
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
        let mut bases_send = Vec::with_capacity(sender_in_leg_indices.len());
        let mut bases_recv = Vec::with_capacity(receiver_in_leg_indices.len());
        let mut bases_at = Vec::with_capacity(legs.len());

        let minus_pk = pk.into_group().neg();
        for i in 0..num_pending_txns {
            if receiver_in_leg_indices.contains(&i) {
                let y = (legs[i].ct_r.into_group() + minus_pk).into_affine();
                enc_total_recv += legs[i].ct_amount;
                bases_recv.push(y);
            } else if sender_in_leg_indices.contains(&i) {
                let y = (legs[i].ct_s.into_group() + minus_pk).into_affine();
                enc_total_send += legs[i].ct_amount;
                bases_send.push(y);
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }

            let y = (legs[i].ct_asset_id.into_group() + minus_h_at).into_affine();
            bases_at.push(y);
        }

        self.pk_send
            .as_ref()
            .map(|t| transcript.append(b"t_pk_send", &t.0));
        self.pk_recv
            .as_ref()
            .map(|t| transcript.append(b"t_pk_recv", &t.0));
        transcript.append(b"t_asset_id", &self.asset_id.0);

        let y_total_send = if let Some(resp) = &self.resp_sent_amount {
            let y_total_send = (enc_total_send
                - (enc_gen * G::ScalarField::from(pending_sent_amount)))
            .into_affine();
            resp.challenge_contribution(&enc_key_gen, &y_total_send, &mut transcript)?;
            Some(y_total_send)
        } else {
            None
        };

        let y_total_recv = if let Some(resp) = &self.resp_recv_amount {
            let y_total_recv = (enc_total_recv
                - (enc_gen * G::ScalarField::from(pending_recv_amount)))
            .into_affine();
            resp.challenge_contribution(&enc_key_gen, &y_total_recv, &mut transcript)?;
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

        let mut challenge_powers = vec![];
        let mut c = G::ScalarField::one();
        for _ in 0..num_pending_txns {
            c *= challenge;
            challenge_powers.push(c);
        }

        let mut scalars_send = Vec::with_capacity(sender_in_leg_indices.len());
        let mut scalars_recv = Vec::with_capacity(receiver_in_leg_indices.len());

        for i in 0..num_pending_txns {
            if receiver_in_leg_indices.contains(&i) {
                scalars_recv.push(challenge_powers[i]);
            } else if sender_in_leg_indices.contains(&i) {
                scalars_send.push(challenge_powers[i]);
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }
        }

        if let Some((t, resp)) = self.pk_send {
            bases_send.push(enc_key_gen);
            scalars_send.push(-resp);
            if t.into_group().neg() != G::Group::msm_unchecked(&bases_send, &scalars_send) {
                return Err(Error::ProofVerificationError(
                    "Sender public key verification failed".to_string(),
                ));
            }
        }

        if let Some((t, resp)) = self.pk_recv {
            bases_recv.push(enc_key_gen);
            scalars_recv.push(-resp);
            if t.into_group().neg() != G::Group::msm_unchecked(&bases_recv, &scalars_recv) {
                return Err(Error::ProofVerificationError(
                    "Receiver public key verification failed".to_string(),
                ));
            }
        }

        bases_at.push(enc_key_gen);
        challenge_powers.push(-self.asset_id.1);
        if self.asset_id.0.into_group().neg()
            != G::Group::msm_unchecked(&bases_at, &challenge_powers)
        {
            return Err(Error::ProofVerificationError(
                "Asset ID verification failed".to_string(),
            ));
        }

        if let Some(resp) = &self.resp_sent_amount {
            if !resp.verify(&y_total_send.unwrap(), &enc_key_gen, &challenge) {
                return Err(Error::ProofVerificationError(
                    "resp_sent_amount verification failed".to_string(),
                ));
            }
        }

        if let Some(resp) = &self.resp_recv_amount {
            if !resp.verify(&y_total_recv.unwrap(), &enc_key_gen, &challenge) {
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
    use crate::keys::keygen_sig;
    use crate::leg::Leg;
    use crate::leg::tests::setup_keys;
    use blake2::Blake2b512;
    use std::time::Instant;

    type PallasA = ark_pallas::Affine;
    type PallasFr = ark_pallas::Fr;

    #[test]
    fn pob_with_auditor_as_verifier() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key(b"testing");

        let asset_id = 1;

        let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        // Account exists with some balance and pending txns
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk, id.clone());
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

        let enc_key_gen = PallasA::rand(&mut rng);
        let enc_gen = PallasA::rand(&mut rng);

        let (
            ((sk, pk), (_, pk_e)),
            ((_sk_r, pk_other), (_, pk_e_other)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let num_pending_txns = 20;

        // Account exists with some balance and pending txns
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk, id.clone());
        account.balance = 1000000;
        account.counter = num_pending_txns;
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        // Create some legs as pending transfers
        let mut legs = vec![];
        // Set this amount in each leg. Just for testing, in practice it could be different
        let amount = 10;
        let mut pending_sent_amount = 0;
        let mut pending_recv_amount = 0;
        let mut sender_in_leg_indices = BTreeSet::new();
        let mut receiver_in_leg_indices = BTreeSet::new();
        for i in 0..num_pending_txns as usize {
            // for odd i, account is sender, for even i, its receiver
            let (leg_enc, leg_enc_rand) = if i % 2 == 0 {
                pending_recv_amount += amount;
                receiver_in_leg_indices.insert(i);
                let leg =
                    Leg::new(pk_other.0, pk.0, vec![(true, pk_a_e.0)], amount, asset_id).unwrap();
                let (leg_enc, leg_enc_rand) = leg
                    .encrypt::<_, Blake2b512>(&mut rng, pk_e_other.0, pk_e.0, enc_key_gen, enc_gen)
                    .unwrap();
                (leg_enc, leg_enc_rand)
            } else {
                pending_sent_amount += amount;
                sender_in_leg_indices.insert(i);
                let leg =
                    Leg::new(pk.0, pk_other.0, vec![(true, pk_a_e.0)], amount, asset_id).unwrap();
                let (leg_enc, leg_enc_rand) = leg
                    .encrypt::<_, Blake2b512>(&mut rng, pk_e.0, pk_e_other.0, enc_key_gen, enc_gen)
                    .unwrap();
                (leg_enc, leg_enc_rand)
            };
            legs.push((leg_enc, leg_enc_rand));
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
            enc_key_gen,
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
                legs.into_iter().map(|l| l.0).collect(),
                sender_in_leg_indices.clone(),
                receiver_in_leg_indices.clone(),
                pending_sent_amount,
                pending_recv_amount,
                nonce,
                account_comm_key,
                enc_key_gen,
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
}
