#![cfg_attr(not(feature = "std"), no_std)]
#![allow(non_snake_case)]

pub const NONCE_LABEL: &'static [u8; 5] = b"nonce";
pub const ASSET_ID_LABEL: &'static [u8; 8] = b"asset_id";
pub const ACCOUNT_COMMITMENT_LABEL: &'static [u8; 18] = b"account_commitment";
pub const PK_LABEL: &'static [u8; 2] = b"pk";
pub const ID_LABEL: &'static [u8; 2] = b"id";
pub const PK_T_LABEL: &'static [u8; 4] = b"pk_t";
pub const PK_T_GEN_LABEL: &'static [u8; 8] = b"pk_t_gen";
pub const LEG_ENC_LABEL: &'static [u8; 7] = b"leg_enc";
pub const INDEX_IN_ASSET_DATA_LABEL: &'static [u8; 19] = b"index_in_asset_data";
pub const RE_RANDOMIZED_PATH_LABEL: &'static [u8; 18] = b"re_randomized_path";
pub const ROOT_LABEL: &'static [u8; 4] = b"root";
pub const ISSUER_PK_LABEL: &'static [u8; 9] = b"issuer_pk";
pub const INCREASE_BAL_BY_LABEL: &'static [u8; 15] = b"increase_bal_by";
pub const UPDATED_ACCOUNT_COMMITMENT_LABEL: &'static [u8; 26] = b"updated_account_commitment";
// In practice, these will be different for different txns
pub const TXN_ODD_LABEL: &[u8; 13] = b"txn-odd-level";
pub const TXN_EVEN_LABEL: &'static [u8; 14] = b"txn-even-level";
pub const TXN_CHALLENGE_LABEL: &'static [u8; 13] = b"txn-challenge";
pub const FEE_AMOUNT_LABEL: &'static [u8; 10] = b"fee_amount";
pub const BALANCE_LABEL: &'static [u8; 7] = b"balance";
pub const PENDING_SENT_AMOUNT_LABEL: &'static [u8; 19] = b"pending_sent_amount";
pub const PENDING_RECV_AMOUNT_LABEL: &'static [u8; 19] = b"pending_recv_amount";
pub const COUNTER_LABEL: &'static [u8; 7] = b"counter";
pub const LEGS_LABEL: &'static [u8; 4] = b"legs";

pub const T_SIG_KEY: &'static [u8; 9] = b"t_sig_key";
pub const T_ENC_KEY: &'static [u8; 9] = b"t_enc_key";

pub mod keys;
pub mod util;

pub mod account;
pub mod account_registration;
mod error;
pub mod leg;
pub mod poseidon_impls;
pub mod fee_account;

pub use error::Error;

pub use polymesh_dart_common::{
    AssetId, Balance, PendingTxnCounter, AMOUNT_BITS, MAX_AMOUNT, MAX_ASSET_ID,
};

// TODO: General question: Should i be hashing a generator/commitment every time i use it so that the instance is always hashed in order of invoking the protocol?

// TODO: Check if root should be added to the transcript before its used.

// TODO: Add protocol specific prefixes to labels

// TODO: Ensure all intermediate secret values are being zeroed.

// Venue creating settlement
// - takes sender key, receiver key, amount, asset id, and auditor/mediator key
// - creates leg enc. and corresponding proof

// User creates keys -- Decide whether proof of knowledge of secret key is required.
// User initiates account state - passes key, etc , gets acc. state and proof.
// User prepares proof for mint txn - takes current acc. state, amount and gives new acc. state, acc. state commitment, proof, etc.
// User prepares proof for affirm-as-sender txn - ...............
// User prepares proof for affirm-as-receiver txn - ...............
