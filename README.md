# Implementation of DART on Polymesh

[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)

A Rust implementation of the DART (Decentralized, Anonymous and Regulation-Friendly Tokenization) protocol for Polymesh's Confidential Assets system.

## Overview

DART is a privacy-preserving protocol that allows for confidential asset transfers while still maintaining regulatory compliance. This library provides the cryptographic primitives and zero-knowledge proof systems that power the Polymesh confidential asset infrastructure.

For detailed information, please refer to the [P-DART paper](https://assets.polymesh.network/P-DART-v1.pdf).

Key features:

- Zero-knowledge proofs for asset transfers
- Confidential asset states with curve tree storage
- Regulatory compliance mechanisms with auditors and mediators
- Fee payment systems for confidential transactions
- Account registration and encryption systems

## Architecture

The library is organized around several key components:

- **Account management**: Public and private keys for accounts and encryption
- **Curve Trees**: Efficient data structures for storing asset and account state commitments
- **Zero-knowledge proofs**: For asset transfers, minting, registration, and more
- **Settlement system**: For handling confidential asset transfers between parties
- **Fee payment**: Mechanisms for confidential fee payments

## Feature Flags

The library provides several feature flags:

- `std` - Use Rust standard library (default)
- `backend_bp` - Enable Bulletproofs backend
- `serde` - Enable serialization/deserialization with serde
- `sqlx` - Enable SQL database integration
- `parallel` - Enable parallel computation for improved performance
- `async_tree` - Enable asynchronous curve tree operations

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## License

This project is licensed under the GNU General Public License v3.0 - see the LICENSE file for details.
