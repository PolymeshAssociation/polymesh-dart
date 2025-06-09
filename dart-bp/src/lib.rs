#![allow(non_snake_case)]

pub mod account_new;
pub mod account_old;
pub mod leg;
pub mod macros;
pub mod old;
pub mod util;

pub type AssetId = u32;
pub type Balance = u64;
pub type PendingTxnCounter = u16;

pub const AMOUNT_BITS: u16 = 48;

pub const MAX_AMOUNT: u64 = (1 << AMOUNT_BITS) - 1;

pub const MAX_ASSET_ID: u32 = ((1_u64 << 32) - 1_u64) as u32;

// TODO: The ephemeral public key created during instance should be added to the transcript.

// Venue creating settlement
// - takes sender key, receiver key, amount, asset id, and auditor/mediator key
// - creates leg enc. and corresponding proof

// User creates keys -- Decide whether proof of knowledge of secret key is required.
// User initiates account state - passes key, etc , gets acc. state and proof.
// User prepares proof for mint txn - takes current acc. state, amount and gives new acc. state, acc. state commitment, proof, etc.
// User prepares proof for affirm-as-sender txn - ...............
// User prepares proof for affirm-as-receiver txn - ...............
