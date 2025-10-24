//! # P-DART Mathematical Documentation
//!
//! This crate contains the mathematical documentation for the DART (Decentralized, Anonymous 
//! and Regulation-Friendly Tokenization) protocol implemented with Bulletproofs.
//!
//! For detailed information, please refer to the [P-DART paper](https://assets.polymesh.network/P-DART-v1.pdf).
//!
//! ## Documentation Sections
//!
//! The documentation is organized into the following sections:
//!
//! - [Notation and Prerequisites](notation) - Mathematical notation and background
//! - [Account Registration](account_registration) - Account creation and proofs
//! - [Asset Minting](asset_minting) - Issuer minting process
//! - [Settlements](settlements) - Settlement and transfer proofs
//! - [Affirmations](affirmations) - Sender/receiver affirmation proofs
//! - [Fee System](fee_system) - Fee account management and payments
//! - [Appendix](appendix) - Additional information and references

#![doc = include_str!("index.md")]

/// Notation, Prerequisites and System Model
///
#[doc = include_str!("1.md")]
pub mod notation {}

/// Account Registration
///
#[doc = include_str!("2.md")]
pub mod account_registration {}

/// Asset Minting
///
#[doc = include_str!("3.md")]
pub mod asset_minting {}

/// Settlement
///
#[doc = include_str!("4.md")]
pub mod settlements {}

/// Sender/Receiver Affirmations
///
#[doc = include_str!("5.md")]
pub mod affirmations {}

/// Fee System
///
#[doc = include_str!("6.md")]
pub mod fee_system {}

/// Appendix
///
#[doc = include_str!("appendix.md")]
pub mod appendix {}
