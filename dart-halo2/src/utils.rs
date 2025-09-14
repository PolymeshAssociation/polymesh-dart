use ark_std::io::Write;
use merlin::Transcript;
use ff::{FromUniformBytes, PrimeField, Field};
use crate::AffineSerializable;
use crate::error::{Result, Error};

/// Adapter to make merlin::Transcript implement ark_std::io::Write
/// This is needed for compatibility with sigma_protocols which expects ark_std::io::Write
pub struct TranscriptWriter<'a>(pub &'a mut Transcript);

impl<'a> Write for TranscriptWriter<'a> {
    fn write(&mut self, buf: &[u8]) -> ark_std::io::Result<usize> {
        self.0.append_message(b"io_write", buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> ark_std::io::Result<()> {
        Ok(())
    }
}

impl<'a> TranscriptWriter<'a> {
    /// Append a message to the transcript
    pub fn append_message(&mut self, label: &'static [u8], message: &[u8]) {
        self.0.append_message(label, message);
    }

    /// Append serializable data to the transcript
    pub fn append_serializable<G: AffineSerializable>(&mut self, data: &G) -> Result<()> {
        self.0.append_message(b"data", data.to_bytes().as_ref());
        Ok(())
    }

    /// Generate a challenge scalar from the transcript
    pub fn generate_challenge<G: AffineSerializable>(&mut self, label: &'static [u8]) -> G::Scalar {
        let mut challenge_bytes = [0u8; 64];
        self.0.challenge_bytes(label, &mut challenge_bytes);
        G::Scalar::from_uniform_bytes(&challenge_bytes)
    }
}

/*
/// Generate responses (Schnorr step 3) for state change just related to amount and balances
pub fn generate_schnorr_responses_for_balance_change<
    F0: PrimeField,
    G0: AffineSerializable<ScalarExt = F0>,
>(
    old_balance: Balance,
    new_balance: Balance,
    amount: Balance,
    comm_balance_blinding: F0,
    t_balance: &CommitmentToRandomness<G0>,
    t_leg_amount: PokDiscreteLogProtocol<G0>,
    prover_challenge: &F0,
) -> Result<(Response<G0>, PokDiscreteLog<G0>)> {
    let resp_balance = t_balance.response(
        &[
            comm_balance_blinding,
            F0::from(amount as u64),
            F0::from(old_balance as u64),
            F0::from(new_balance as u64),
        ],
        prover_challenge,
    )?;
    
    let resp_leg_amount = t_leg_amount.gen_proof(prover_challenge);
    
    Ok((resp_balance, resp_leg_amount))
}

/// Generate responses (Schnorr step 3) for state change excluding changes related to amount and balances
pub fn generate_schnorr_responses_for_common_state_change<
    F0: PrimeField,
    G0: AffineSerializable<ScalarExt = F0>,
>(
    account: &AccountState<G0>,
    updated_account: &AccountState<G0>,
    leaf_rerandomization: F0,
    comm_bp_blinding: F0,
    t_r_leaf: &CommitmentToRandomness<G0>,
    t_acc_new: &CommitmentToRandomness<G0>,
    t_null: PokDiscreteLogProtocol<G0>,
    t_leg_asset_id: PokDiscreteLogProtocol<G0>,
    t_leg_pk: PokDiscreteLogProtocol<G0>,
    t_bp_randomness_relations: &CommitmentToRandomness<G0>,
    prover_challenge: &F0,
) -> Result<(
    Response<G0>,
    Response<G0>,
    PokDiscreteLog<G0>,
    PokDiscreteLog<G0>,
    PokDiscreteLog<G0>,
    Response<G0>,
)> {
    // TODO: Eliminate duplicate responses
    let resp_leaf = t_r_leaf.response(
        &[
            account.sk,
            F0::from(account.balance as u64),
            F0::from(account.counter as u64),
            F0::from(account.asset_id as u64),
            account.rho,
            account.current_rho,
            account.randomness,
            leaf_rerandomization,
        ],
        prover_challenge,
    )?;
    
    let resp_acc_new = t_acc_new.response(
        &[
            updated_account.sk,
            F0::from(updated_account.balance as u64),
            F0::from(updated_account.counter as u64),
            F0::from(updated_account.asset_id as u64),
            updated_account.rho,
            updated_account.current_rho,
            updated_account.randomness,
        ],
        prover_challenge,
    )?;
    
    let resp_null = t_null.gen_proof(prover_challenge);
    let resp_leg_asset_id = t_leg_asset_id.gen_proof(prover_challenge);
    let resp_leg_pk = t_leg_pk.gen_proof(prover_challenge);
    
    let resp_bp = t_bp_randomness_relations.response(
        &[
            comm_bp_blinding,
            updated_account.rho,
            account.current_rho,
            updated_account.current_rho,
            account.randomness,
            updated_account.randomness,
        ],
        prover_challenge,
    )?;
    
    Ok((
        resp_leaf,
        resp_acc_new,
        resp_null,
        resp_leg_asset_id,
        resp_leg_pk,
        resp_bp,
    ))
}

/// Take challenge contribution of Schnorr t values for balance change
pub fn take_challenge_contrib_of_schnorr_t_values_for_balance_change<G0: AffineSerializable>(
    ct_amount: &G0,
    t_comm_bp_bal: &CommitmentToRandomness<G0>,
    resp_leg_amount: &PokPedersenCommitment<G0>,
    enc_key_gen: G0,
    enc_gen: G0,
    transcript_writer: &mut TranscriptWriter,
) -> Result<()> {
    // TODO: Add proper challenge contribution for t_comm_bp_bal
    // For now, we skip the challenge contribution since CommitmentToRandomness doesn't have challenge_contribution method
    
    // Add challenge contribution for leg amount
    resp_leg_amount.challenge_contribution(
        &enc_key_gen,
        &enc_gen,
        ct_amount,
        transcript_writer,
    )?;
    
    Ok(())
}

/// Verify Schnorr for common state change
pub fn verify_schnorr_for_common_state_change<G0: AffineSerializable>(
    leg_enc: &LegEncryption<G0>,
    is_sender: bool,
    has_counter_decreased: bool,
    nullifier: &G0,
    re_randomized_leaf: &G0,
    updated_account_commitment: &G0,
    comm_bp: &G0,
    t_r_leaf: &CommitmentToRandomness<G0>,
    t_acc_new: &CommitmentToRandomness<G0>,
    t_bp: &CommitmentToRandomness<G0>,
    resp_leaf: &Response<G0>,
    resp_acc_new: &Response<G0>,
    resp_null: &PokDiscreteLog<G0>,
    resp_leg_asset_id: &PokDiscreteLog<G0>,
    resp_leg_pk: &PokDiscreteLog<G0>,
    resp_bp: &Response<G0>,
    verifier_challenge: &G0::ScalarExt,
    account_comm_key: &impl AccountCommitmentKeyTrait<G0>,
    enc_key_gen: G0,
    enc_gen: G0,
) -> Result<()> {
    // TODO: Add proper verification logic
    // For now, we skip the verification since we need to understand how to properly verify commitments
    
    // Verify that secret key and asset ID are consistent between old and new account commitments
    // This would require access to the response scalars, which may not be directly accessible
    
    // TODO: Add more consistency checks as needed
    
    Ok(())
}

/// Verify Schnorr for balance change
pub fn verify_schnorr_for_balance_change<G0: AffineSerializable>(
    leg_enc: &LegEncryption<G0>,
    resp_comm_bp_bal: &Response<G0>,
    resp_leg_amount: &PokDiscreteLog<G0>,
    verifier_challenge: &G0::ScalarExt,
    enc_key_gen: G0,
    enc_gen: G0,
) -> Result<()> {
    // TODO: Add proper verification logic
    // For now, we skip the verification since we need to understand how to properly verify commitments
    
    Ok(())
}

/// Generate commitment to randomness (Schnorr step 1) for state change excluding changes related to amount and balances
pub fn generate_schnorr_t_values_for_common_state_change<
    R: CryptoRngCore,
    F0: PrimeField,
    G0: AffineSerializable<ScalarExt = F0>,
>(
    rng: &mut R,
    asset_id: AssetId,
    leg_enc: &LegEncryption<G0>,
    old_account: &AccountState<G0>,
    updated_account: &AccountState<G0>,
    is_sender: bool,
    sk_blinding: F0,
    old_balance_blinding: F0,
    new_balance_blinding: F0,
    new_counter_blinding: F0,
    initial_rho_blinding: F0,
    old_rho_blinding: F0,
    new_rho_blinding: F0,
    old_randomness_blinding: F0,
    new_randomness_blinding: F0,
    asset_id_blinding: F0,
    r_pk: F0, // r_1 or r_2 depending on sender or receiver
    r_4: F0,
    account_comm_key: &impl AccountCommitmentKeyTrait<G0>,
    enc_key_gen: G0,
    enc_gen: G0,
) -> Result<(
    G0, // nullifier
    G0, // comm_bp_randomness_relations
    F0, // comm_bp_blinding
    CommitmentToRandomness<G0>, // t_r_leaf
    CommitmentToRandomness<G0>, // t_acc_new
    PokDiscreteLogProtocol<G0>, // t_null
    PokDiscreteLogProtocol<G0>, // t_leg_asset_id
    PokDiscreteLogProtocol<G0>, // t_leg_pk
    CommitmentToRandomness<G0>, // t_bp_randomness_relations
)> {
    let nullifier = old_account.nullifier(account_comm_key);

    // TODO: Add proper Bulletproof commitment logic
    // For now, we create dummy commitments
    let comm_bp_randomness_relations = enc_gen; // TODO: Replace with actual Bulletproof commitment
    let comm_bp_blinding = Field::random(&mut *rng);

    // Schnorr commitment for proving correctness of re-randomized leaf
    let t_r_leaf = CommitmentToRandomness::new(
        &[
            account_comm_key.sk_gen(),
            account_comm_key.balance_gen(),
            account_comm_key.counter_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.current_rho_gen(),
            account_comm_key.randomness_gen(),
            account_comm_key.randomness_gen(), // TODO: Replace with proper rerandomization generator
        ],
        vec![
            sk_blinding,
            old_balance_blinding,
            new_counter_blinding,
            initial_rho_blinding,
            old_rho_blinding,
            old_randomness_blinding,
            Field::random(&mut *rng),
        ],
    );

    // Schnorr commitment for proving correctness of new account state
    let t_acc_new = CommitmentToRandomness::new(
        &[
            account_comm_key.sk_gen(),
            account_comm_key.balance_gen(),
            account_comm_key.counter_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.current_rho_gen(),
            account_comm_key.randomness_gen(),
        ],
        vec![
            sk_blinding,
            new_balance_blinding,
            new_counter_blinding,
            initial_rho_blinding,
            new_rho_blinding,
            new_randomness_blinding,
        ],
    );

    // Schnorr commitment for proving correctness of nullifier
    let t_null = PokDiscreteLogProtocol::init(
        old_account.current_rho,
        old_rho_blinding,
        &account_comm_key.current_rho_gen(),
    );

    // Schnorr commitment for proving knowledge of asset-id in leg
    let t_leg_asset_id = PokDiscreteLogProtocol::init(
        F0::from(asset_id as u64),
        asset_id_blinding,
        &enc_gen,
    );

    // Schnorr commitment for proving knowledge of secret key in leg
    let t_leg_pk = PokDiscreteLogProtocol::init(
        old_account.sk,
        r_pk,
        &enc_key_gen,
    );

    // Schnorr commitment for proving randomness relations
    let t_bp_randomness_relations = CommitmentToRandomness::new(
        &[
            account_comm_key.rho_gen(),
            account_comm_key.current_rho_gen(),
            account_comm_key.current_rho_gen(), // new current_rho
            account_comm_key.randomness_gen(),
            account_comm_key.randomness_gen(),  // new randomness
        ],
        vec![
            initial_rho_blinding,
            old_rho_blinding,
            new_rho_blinding,
            old_randomness_blinding,
            new_randomness_blinding,
        ],
    );

    Ok((
        nullifier,
        comm_bp_randomness_relations,
        comm_bp_blinding,
        t_r_leaf,
        t_acc_new,
        t_null,
        t_leg_asset_id,
        t_leg_pk,
        t_bp_randomness_relations,
    ))
}

/// Generate commitment to randomness (Schnorr step 1) for state change just related to amount and balances
pub fn generate_schnorr_t_values_for_balance_change<
    R: CryptoRngCore,
    F0: PrimeField,
    G0: AffineSerializable<ScalarExt = F0>,
>(
    rng: &mut R,
    amount: Balance,
    ct_amount: &G0,
    old_balance_blinding: F0,
    new_balance_blinding: F0,
    amount_blinding: F0,
    r_3: F0,
    enc_key_gen: G0,
    enc_gen: G0,
    transcript_writer: &mut TranscriptWriter,
) -> Result<(CommitmentToRandomness<G0>, PokDiscreteLogProtocol<G0>)> {
    // Schnorr commitment for proving knowledge of amount, old account balance and new account balance
    let t_balance = CommitmentToRandomness::new(
        &[
            enc_gen, // blinding generator
            enc_gen, // amount generator
            enc_gen, // old balance generator  
            enc_gen, // new balance generator
        ],
        vec![
            F0::random(&mut *rng), // blinding
            amount_blinding,
            old_balance_blinding,
            new_balance_blinding,
        ],
    );

    // Schnorr commitment for proving knowledge of amount used in the leg
    let t_leg_amount = PokDiscreteLogProtocol::init(
        r_3,
        F0::random(&mut *rng),
        &enc_key_gen,
    );

    // Add challenge contribution of each of the above commitments to the transcript
    // Note: CommitmentToRandomness doesn't have challenge_contribution method
    // The commitment values will be used during response generation
    // TODO: Add proper challenge contribution if needed for transcript consistency
    
    Ok((t_balance, t_leg_amount))
}*/
