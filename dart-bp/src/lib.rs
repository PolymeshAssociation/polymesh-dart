#![cfg_attr(not(feature = "std"), no_std)]
#![allow(non_snake_case)]

pub mod account;
pub mod keys;
pub mod leg;
pub mod macros;
pub mod util;

pub use polymesh_dart_common::{
    AMOUNT_BITS, AssetId, Balance, MAX_AMOUNT, MAX_ASSET_ID, PendingTxnCounter,
};

// TODO: The ephemeral public key created during instance should be added to the transcript.

// Venue creating settlement
// - takes sender key, receiver key, amount, asset id, and auditor/mediator key
// - creates leg enc. and corresponding proof

// User creates keys -- Decide whether proof of knowledge of secret key is required.
// User initiates account state - passes key, etc , gets acc. state and proof.
// User prepares proof for mint txn - takes current acc. state, amount and gives new acc. state, acc. state commitment, proof, etc.
// User prepares proof for affirm-as-sender txn - ...............
// User prepares proof for affirm-as-receiver txn - ...............
