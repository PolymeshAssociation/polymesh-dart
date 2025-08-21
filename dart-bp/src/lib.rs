#![cfg_attr(not(feature = "std"), no_std)]
#![allow(non_snake_case)]

pub mod keys;
pub mod util;

pub mod account;
pub mod account_registration;
mod error;
pub mod leg;
pub mod poseidon_impls;

pub use error::Error;

pub use polymesh_dart_common::{
    AMOUNT_BITS, AssetId, Balance, MAX_AMOUNT, MAX_ASSET_ID, PendingTxnCounter,
};

// TODO: General question: Should i be hashing a generator/commitment every time i use it so that the instance is always hashed in order of invoking the protocol?

// TODO: Check if root should be added to the transcript before its used.

// Venue creating settlement
// - takes sender key, receiver key, amount, asset id, and auditor/mediator key
// - creates leg enc. and corresponding proof

// User creates keys -- Decide whether proof of knowledge of secret key is required.
// User initiates account state - passes key, etc , gets acc. state and proof.
// User prepares proof for mint txn - takes current acc. state, amount and gives new acc. state, acc. state commitment, proof, etc.
// User prepares proof for affirm-as-sender txn - ...............
// User prepares proof for affirm-as-receiver txn - ...............
