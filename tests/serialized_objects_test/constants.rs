use polymesh_dart::*;

pub const V1_DIR: &str = "tests/serialized_objects/v1";
pub const SEED: [u8; 32] = [1u8; 32];
pub const IDENTITY: &[u8] = b"test-identity-v1";
pub const BALANCE: Balance = 1000;
pub const NONCE: &[u8] = b"test-nonce-v1";
pub const FEE_REG_BATCH_SIZE: usize = 2;
pub const ASSET_BATCH_SIZE: usize = 2;
pub const TOPUP_AMOUNT: Balance = 500;
pub const PAYMENT_AMOUNT: Balance = 100;
pub const MINT_AMOUNT: Balance = 500;
pub const SETTLEMENT_AMOUNT: Balance = 500;
// Asset ids correspond to the leaf indices of the asset tree
pub const ASSET_ID_0: AssetId = 0;
pub const ASSET_ID_1: AssetId = 1;
pub const ASSET_ID_2: AssetId = 2;

pub const ALICE_SEED: &str = "alice-seed";
pub const BOB_SEED: &str = "bob-seed";
pub const CAROL_SEED: &str = "carol-seed";
pub const DAVE_SEED: &str = "dave-seed";

pub const EVE_SEED: &str = "eve-seed";

pub const ACCOUNT_KEYS: &str = "account_keys.bin";
pub const ACCOUNT_KEY_PAIR: &str = "account_key_pair.bin";
pub const ENCRYPTION_KEY_PAIR: &str = "encryption_key_pair.bin";
pub const ACCOUNT_PUBLIC_KEYS: &str = "account_public_keys.bin";
pub const ACCOUNT_STATE: &str = "account_state.bin";
pub const ACCOUNT_STATE_COMMITMENT: &str = "account_state_commitment.bin";
pub const ACCOUNT_STATE_NULLIFIER: &str = "account_state_nullifier.bin";
pub const ACCOUNT_ASSET_STATE_NO_PENDING: &str = "account_asset_state_no_pending.bin";
pub const ACCOUNT_ASSET_STATE_WITH_PENDING: &str = "account_asset_state_with_pending.bin";
pub const ASSET_COMMITMENT_DATA_PREFIX: &str = "asset_commitment_data";
pub const ASSET_COMMITMENT_PARAMETERS: &str = "asset_commitment_parameters.bin";
pub const DART_BP_GENERATORS: &str = "dart_bp_generators.bin";

pub const FEE_REG_SPLIT_REQUEST: &str = "fee_reg_split_request.bin";
pub const FEE_REG_SPLIT_RESPONSE: &str = "fee_reg_split_response.bin";
pub const FEE_REG_SPLIT_PROOF: &str = "fee_reg_split_proof.bin";

pub const FEE_TOPUP_SPLIT_REQUEST: &str = "fee_topup_split_request.bin";
pub const FEE_TOPUP_SPLIT_RESPONSE: &str = "fee_topup_split_response.bin";
pub const FEE_TOPUP_SPLIT_PROOF: &str = "fee_topup_split_proof.bin";

pub const FEE_PAYMENT_SPLIT_REQUEST: &str = "fee_payment_split_request.bin";
pub const FEE_PAYMENT_SPLIT_RESPONSE: &str = "fee_payment_split_response.bin";
pub const FEE_PAYMENT_SPLIT_PROOF: &str = "fee_payment_split_proof.bin";

pub const ACCOUNT_REG_SPLIT_REQUEST: &str = "account_reg_split_request.bin";
pub const ACCOUNT_REG_SPLIT_RESPONSE: &str = "account_reg_split_response.bin";
pub const ACCOUNT_REG_SPLIT_PROOF: &str = "account_reg_split_proof.bin";

pub const MINT_SPLIT_REQUEST: &str = "mint_split_request.bin";
pub const MINT_SPLIT_RESPONSE: &str = "mint_split_response.bin";
pub const MINT_SPLIT_PROOF: &str = "mint_split_proof.bin";

pub const SENDER_AFFIRM_SPLIT_REQUEST: &str = "sender_affirm_split_request.bin";
pub const SENDER_AFFIRM_SPLIT_RESPONSE: &str = "sender_affirm_split_response.bin";
pub const SENDER_AFFIRM_SPLIT_PROOF: &str = "sender_affirm_split_proof.bin";

pub const RECEIVER_AFFIRM_SPLIT_REQUEST: &str = "receiver_affirm_split_request.bin";
pub const RECEIVER_AFFIRM_SPLIT_RESPONSE: &str = "receiver_affirm_split_response.bin";
pub const RECEIVER_AFFIRM_SPLIT_PROOF: &str = "receiver_affirm_split_proof.bin";

pub const RECEIVER_COUNTER_UPDATE_SPLIT_REQUEST: &str = "receiver_counter_update_split_request.bin";
pub const RECEIVER_COUNTER_UPDATE_SPLIT_RESPONSE: &str =
    "receiver_counter_update_split_response.bin";
pub const RECEIVER_COUNTER_UPDATE_SPLIT_PROOF: &str = "receiver_counter_update_split_proof.bin";

pub const CLAIM_RECEIVED_SPLIT_REQUEST: &str = "claim_received_split_request.bin";
pub const CLAIM_RECEIVED_SPLIT_RESPONSE: &str = "claim_received_split_response.bin";
pub const CLAIM_RECEIVED_SPLIT_PROOF: &str = "claim_received_split_proof.bin";

pub const SENDER_REVERSE_SPLIT_REQUEST: &str = "sender_reverse_split_request.bin";
pub const SENDER_REVERSE_SPLIT_RESPONSE: &str = "sender_reverse_split_response.bin";
pub const SENDER_REVERSE_SPLIT_PROOF: &str = "sender_reverse_split_proof.bin";

pub const SENDER_COUNTER_UPDATE_SPLIT_REQUEST: &str = "sender_counter_update_split_request.bin";
pub const SENDER_COUNTER_UPDATE_SPLIT_RESPONSE: &str = "sender_counter_update_split_response.bin";
pub const SENDER_COUNTER_UPDATE_SPLIT_PROOF: &str = "sender_counter_update_split_proof.bin";

pub const INSTANT_SENDER_AFFIRM_SPLIT_REQUEST: &str = "instant_sender_affirm_split_request.bin";
pub const INSTANT_SENDER_AFFIRM_SPLIT_RESPONSE: &str = "instant_sender_affirm_split_response.bin";
pub const INSTANT_SENDER_AFFIRM_SPLIT_PROOF: &str = "instant_sender_affirm_split_proof.bin";

pub const INSTANT_RECEIVER_AFFIRM_SPLIT_REQUEST: &str = "instant_receiver_affirm_split_request.bin";
pub const INSTANT_RECEIVER_AFFIRM_SPLIT_RESPONSE: &str =
    "instant_receiver_affirm_split_response.bin";
pub const INSTANT_RECEIVER_AFFIRM_SPLIT_PROOF: &str = "instant_receiver_affirm_split_proof.bin";

pub const LEG_ENCRYPTED: &str = "leg_encrypted.bin";
pub const MEDIATOR_ENCRYPTION: &str = "mediator_encryption.bin";

pub const ACCOUNT_REGISTRATION_PROOF: &str = "account_registration_proof.bin";
pub const ENCRYPTION_KEY_REGISTRATION_PROOF: &str = "encryption_key_registration_proof.bin";
pub const FEE_ACCOUNT_REGISTRATION_PROOF: &str = "fee_account_registration_proof.bin";
pub const BATCHED_FEE_ACCOUNT_REGISTRATION_PROOF: &str = "batched_fee_account_registration_proof";
pub const ACCOUNT_ASSET_REGISTRATION_PROOF: &str = "account_asset_registration_proof.bin";
pub const BATCHED_ACCOUNT_ASSET_REGISTRATION_PROOF: &str =
    "batched_account_asset_registration_proof";
pub const KEY_DISTRIBUTION_PROOF_PREFIX: &str = "key_distribution_proof";
pub const FEE_ACCOUNT_TOPUP_PROOF: &str = "fee_account_topup_proof.bin";
pub const FEE_ACCOUNT_PAYMENT_PROOF: &str = "fee_account_payment_proof.bin";
pub const ASSET_MINTING_PROOF: &str = "asset_minting_proof.bin";
pub const SETTLEMENT_PROOF_PREFIX: &str = "settlement_proof";
pub const SETTLEMENT_PROOF_REVEALED_ASSET_ID: &str = "settlement_proof_revealed_asset_id.bin";
pub const SETTLEMENT_PROOF_PARTIES_HIDDEN: &str = "settlement_proof_parties_hidden.bin";
pub const SETTLEMENT_PROOF_2_AUDITORS: &str = "settlement_proof_2_auditors.bin";
