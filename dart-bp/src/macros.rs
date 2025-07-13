#[macro_export]
macro_rules! take_challenge_contrib_of_schnorr_t_values_for_common_state_change {
    ($self: ident, $leg_enc: ident, $is_sender: expr, $nullifier: expr, $sig_null_gen: ident, $asset_value_gen: ident, $verifier_transcript: ident) => {
        $self
            .t_r_leaf
            .serialize_compressed(&mut $verifier_transcript)?;
        $self
            .t_acc_new
            .serialize_compressed(&mut $verifier_transcript)?;
        $self.resp_null.challenge_contribution(
            &$sig_null_gen,
            &$nullifier,
            &mut $verifier_transcript,
        )?;
        $self.resp_leg_asset_id.challenge_contribution(
            &$leg_enc.ct_asset_id.eph_pk,
            &$asset_value_gen,
            &$leg_enc.ct_asset_id.encrypted,
            &mut $verifier_transcript,
        )?;
        $self.resp_leg_pk.challenge_contribution(
            if $is_sender {
                &$leg_enc.ct_s.eph_pk
            } else {
                &$leg_enc.ct_r.eph_pk
            },
            &$sig_null_gen,
            if $is_sender {
                &$leg_enc.ct_s.encrypted
            } else {
                &$leg_enc.ct_r.encrypted
            },
            &mut $verifier_transcript,
        )?;
    };
}

#[macro_export]
macro_rules! take_challenge_contrib_of_schnorr_t_values_for_balance_change {
    ($self: ident, $leg_enc: ident, $pc_gens: path, $asset_value_gen: ident, $verifier_transcript: ident) => {
        $self.resp_old_bal.challenge_contribution(
            &$pc_gens.B,
            &$pc_gens.B_blinding,
            &$self.comm_bal_old,
            &mut $verifier_transcript,
        )?;
        $self.resp_new_bal.challenge_contribution(
            &$pc_gens.B,
            &$pc_gens.B_blinding,
            &$self.comm_bal_new,
            &mut $verifier_transcript,
        )?;
        $self.resp_amount.challenge_contribution(
            &$pc_gens.B,
            &$pc_gens.B_blinding,
            &$self.comm_amount,
            &mut $verifier_transcript,
        )?;
        $self.resp_leg_amount.challenge_contribution(
            &$leg_enc.ct_amount.eph_pk,
            &$asset_value_gen,
            &$leg_enc.ct_amount.encrypted,
            &mut $verifier_transcript,
        )?;
    };
}

#[macro_export]
macro_rules! verify_schnorr_for_common_state_change {
    ($self: ident, $leg_enc: ident, $is_sender: expr, $account_comm_key: ident, $updated_account_commitment: expr, $nullifier: expr, $pc_gens: path, $sig_null_gen: ident, $asset_value_gen: ident, $verifier_challenge: ident) => {
        $self.resp_leaf.is_valid(
            &[
                $account_comm_key.sk_gen(),
                $account_comm_key.balance_gen(),
                $account_comm_key.counter_gen(),
                $account_comm_key.asset_id_gen(),
                $account_comm_key.rho_gen(),
                $account_comm_key.randomness_gen(),
                $pc_gens.B_blinding,
            ],
            &$self.re_randomized_path.re_randomized_leaf,
            &$self.t_r_leaf,
            &$verifier_challenge,
        )?;
        $self.resp_acc_new.is_valid(
            &[
                $account_comm_key.sk_gen(),
                $account_comm_key.balance_gen(),
                $account_comm_key.counter_gen(),
                $account_comm_key.asset_id_gen(),
                $account_comm_key.rho_gen(),
                $account_comm_key.randomness_gen(),
            ],
            &$updated_account_commitment.0,
            &$self.t_acc_new,
            &$verifier_challenge,
        )?;
        if !$self
            .resp_null
            .verify(&$nullifier, &$sig_null_gen, &$verifier_challenge)
        {
            return Err(Error::ProofVerificationError(
                "Nullifier verification failed".to_string(),
            ));
        }
        if !$self.resp_leg_asset_id.verify(
            &$leg_enc.ct_asset_id.encrypted,
            &$leg_enc.ct_asset_id.eph_pk,
            &$asset_value_gen,
            &$verifier_challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "Leg asset ID verification failed".to_string(),
            ));
        }
        if !$self.resp_leg_pk.verify(
            if $is_sender {
                &$leg_enc.ct_s.encrypted
            } else {
                &$leg_enc.ct_r.encrypted
            },
            if $is_sender {
                &$leg_enc.ct_s.eph_pk
            } else {
                &$leg_enc.ct_r.eph_pk
            },
            &$sig_null_gen,
            &$verifier_challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "Leg public key verification failed".to_string(),
            ));
        }

        // Sk and asset id in leaf match the ones in updated account commitment
        if $self.resp_leaf.0[0] != $self.resp_acc_new.0[0] {
            return Err(Error::ProofVerificationError(
                "Secret key in leaf does not match the one in updated account commitment"
                    .to_string(),
            ));
        }
        if $self.resp_leaf.0[3] != $self.resp_acc_new.0[3] {
            return Err(Error::ProofVerificationError(
                "Asset ID in leaf does not match the one in updated account commitment".to_string(),
            ));
        }

        // rho matches the one in nullifier
        if $self.resp_leaf.0[4] != $self.resp_null.response {
            return Err(Error::ProofVerificationError(
                "Rho in leaf does not match the one in nullifier".to_string(),
            ));
        }

        // Asset id in leg is same as in account commitment
        if $self.resp_leg_asset_id.response2 != $self.resp_acc_new.0[3] {
            return Err(Error::ProofVerificationError(
                "Asset ID in leg does not match the one in account commitment".to_string(),
            ));
        }

        // sk in account comm matches the one in pk
        if $self.resp_leg_pk.response2 != $self.resp_leaf.0[0] {
            return Err(Error::ProofVerificationError(
                "Secret key in leg public key does not match the one in leaf".to_string(),
            ));
        }
    };
}

#[macro_export]
macro_rules! verify_schnorr_for_balance_change {
    ($self: ident, $leg_enc: ident, $pc_gens: path, $asset_value_gen: ident, $verifier_challenge: ident) => {
        if !$self.resp_old_bal.verify(
            &$self.comm_bal_old,
            &$pc_gens.B,
            &$pc_gens.B_blinding,
            &$verifier_challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "Old balance verification failed".to_string(),
            ));
        }
        if !$self.resp_new_bal.verify(
            &$self.comm_bal_new,
            &$pc_gens.B,
            &$pc_gens.B_blinding,
            &$verifier_challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "New balance verification failed".to_string(),
            ));
        }
        if !$self.resp_amount.verify(
            &$self.comm_amount,
            &$pc_gens.B,
            &$pc_gens.B_blinding,
            &$verifier_challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "Amount verification failed".to_string(),
            ));
        }

        if !$self.resp_leg_amount.verify(
            &$leg_enc.ct_amount.encrypted,
            &$leg_enc.ct_amount.eph_pk,
            &$asset_value_gen,
            &$verifier_challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "Leg amount verification failed".to_string(),
            ));
        }
    };
}
