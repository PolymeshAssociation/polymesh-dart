use std::fs;

mod account;
mod constants;
mod fee;
mod leg;
mod split;
mod utils;

// Run as `cargo test --test serialized_objects_test generate_v1_serialized_objects -- --ignored`
#[test]
#[ignore = "Run explicitly to regenerate test vectors"]
fn generate_v1_serialized_objects() {
    fs::create_dir_all(constants::V1_DIR).unwrap();
    account::gen_plain_objects();
    account::gen_account_registration_proof();
    account::gen_encryption_key_registration_proof();
    account::gen_fee_account_registration_proof();
    account::gen_batched_fee_account_registration_proof();
    account::gen_account_asset_registration_proof();
    account::gen_batched_account_asset_registration_proof();
    account::gen_key_distribution_proof_2_recipients();
    account::gen_key_distribution_proof_3_recipients();
    account::gen_asset_minting_proof();
    fee::gen_fee_account_topup_proof();
    fee::gen_fee_account_payment_proof();
    leg::gen_settlement_proof();
    leg::gen_settlement_proof_2_legs();
    leg::gen_settlement_proof_3_legs();
    leg::gen_settlement_proof_with_auditor();
    leg::gen_settlement_proof_2_auditors();
    leg::gen_settlement_proof_1_aud_1_med_1_pub();
    leg::gen_settlement_proof_revealed_asset_id();
    leg::gen_settlement_proof_parties_hidden();
    leg::gen_leg_encrypted();
    leg::gen_mediator_encryption();
    split::gen_fee_reg_split();
    split::gen_fee_topup_split();
    split::gen_fee_payment_split();
    split::gen_account_reg_split();
    split::gen_mint_split();
    split::gen_sender_affirm_split();
    split::gen_receiver_affirm_split();
    split::gen_receiver_counter_update_split();
    split::gen_claim_received_split();
    split::gen_sender_reverse_split();
    split::gen_sender_counter_update_split();
    split::gen_instant_sender_affirm_split();
    split::gen_instant_receiver_affirm_split();
}
