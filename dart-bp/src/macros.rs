#[macro_export]
macro_rules! take_challenge_contrib_of_schnorr_t_values_for_common_state_change {
    ($self: ident, $leg_enc: ident, $is_sender: expr, $sig_null_gen: ident, $asset_value_gen: ident, $verifier_transcript: ident) => {
        $self
            .t_r_leaf
            .serialize_compressed(&mut $verifier_transcript)
            .unwrap();
        $self
            .t_acc_new
            .serialize_compressed(&mut $verifier_transcript)
            .unwrap();
        $self
            .resp_null
            .challenge_contribution(&$sig_null_gen, &$self.nullifier, &mut $verifier_transcript)
            .unwrap();
        $self
            .resp_leg_asset_id
            .challenge_contribution(
                &$leg_enc.ct_asset_id.eph_pk,
                &$asset_value_gen,
                &$leg_enc.ct_asset_id.encrypted,
                &mut $verifier_transcript,
            )
            .unwrap();
        $self
            .resp_leg_pk
            .challenge_contribution(
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
            )
            .unwrap();
    };
}

#[macro_export]
macro_rules! take_challenge_contrib_of_schnorr_t_values_for_balance_change {
    ($self: ident, $leg_enc: ident, $pc_gens: path, $asset_value_gen: ident, $verifier_transcript: ident) => {
        $self
            .resp_old_bal
            .challenge_contribution(
                &$pc_gens.B,
                &$pc_gens.B_blinding,
                &$self.comm_bal_old,
                &mut $verifier_transcript,
            )
            .unwrap();
        $self
            .resp_new_bal
            .challenge_contribution(
                &$pc_gens.B,
                &$pc_gens.B_blinding,
                &$self.comm_bal_new,
                &mut $verifier_transcript,
            )
            .unwrap();
        $self
            .resp_amount
            .challenge_contribution(
                &$pc_gens.B,
                &$pc_gens.B_blinding,
                &$self.comm_amount,
                &mut $verifier_transcript,
            )
            .unwrap();
        $self
            .resp_leg_amount
            .challenge_contribution(
                &$leg_enc.ct_amount.eph_pk,
                &$asset_value_gen,
                &$leg_enc.ct_amount.encrypted,
                &mut $verifier_transcript,
            )
            .unwrap();
    };
}

#[macro_export]
macro_rules! verify_schnorr_for_common_state_change {
    ($self: ident, $leg_enc: ident, $is_sender: expr, $account_comm_key: ident, $pc_gens: path, $sig_null_gen: ident, $asset_value_gen: ident, $verifier_challenge: ident) => {
        $self
            .resp_leaf
            .is_valid(
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
            )
            .unwrap();
        $self
            .resp_acc_new
            .is_valid(
                &[
                    $account_comm_key.sk_gen(),
                    $account_comm_key.balance_gen(),
                    $account_comm_key.counter_gen(),
                    $account_comm_key.asset_id_gen(),
                    $account_comm_key.rho_gen(),
                    $account_comm_key.randomness_gen(),
                ],
                &$self.updated_account_commitment.0,
                &$self.t_acc_new,
                &$verifier_challenge,
            )
            .unwrap();
        assert!(
            $self
                .resp_null
                .verify(&$self.nullifier, &$sig_null_gen, &$verifier_challenge,)
        );
        assert!($self.resp_leg_asset_id.verify(
            &$leg_enc.ct_asset_id.encrypted,
            &$leg_enc.ct_asset_id.eph_pk,
            &$asset_value_gen,
            &$verifier_challenge
        ));
        assert!($self.resp_leg_pk.verify(
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
            &$verifier_challenge
        ));

        // Sk and asset id in leaf match the ones in updated account commitment
        assert_eq!($self.resp_leaf.0[0], $self.resp_acc_new.0[0]);
        assert_eq!($self.resp_leaf.0[3], $self.resp_acc_new.0[3]);

        // rho matches the one in nullifier
        assert_eq!($self.resp_leaf.0[4], $self.resp_null.response);

        // Asset id in leg is same as in account commitment
        assert_eq!($self.resp_leg_asset_id.response2, $self.resp_acc_new.0[3]);

        // sk in account comm matches the one in pk
        assert_eq!($self.resp_leg_pk.response2, $self.resp_leaf.0[0]);
    };
}

#[macro_export]
macro_rules! verify_schnorr_for_balance_change {
    ($self: ident, $leg_enc: ident, $pc_gens: path, $asset_value_gen: ident, $verifier_challenge: ident) => {
        assert!($self.resp_old_bal.verify(
            &$self.comm_bal_old,
            &$pc_gens.B,
            &$pc_gens.B_blinding,
            &$verifier_challenge,
        ));
        assert!($self.resp_new_bal.verify(
            &$self.comm_bal_new,
            &$pc_gens.B,
            &$pc_gens.B_blinding,
            &$verifier_challenge,
        ));
        assert!($self.resp_amount.verify(
            &$self.comm_amount,
            &$pc_gens.B,
            &$pc_gens.B_blinding,
            &$verifier_challenge
        ));

        assert!($self.resp_leg_amount.verify(
            &$leg_enc.ct_amount.encrypted,
            &$leg_enc.ct_amount.eph_pk,
            &$asset_value_gen,
            &$verifier_challenge
        ));
    };
}
