---
layout: default
title: DART-BP Math Documentation
---

# P-DART Math Documentation

This documentation contains the mathematical description for the zero knowledge proof of [P-DART](https://assets.polymesh.network/P-DART-v1.pdf), implemented with Bulletproofs.

## Table of Contents

1. **[Notation, Prerequisites and System Model](1.md)**
   - [Notation](1.md#notation)
   - [Sigma protocols](1.md#sigma-protocol)
   - [ElGamal encryption variants](1.md#elgamal-and-its-variations)
   - [Curve Trees as accumulators](1.md#curve-trees)
   - [Bulletproofs](1.md#bulletproofs)
   - [System entities](1.md#system-model)

2. **[Account Registration](2.md)**
   - [Account creation](2.md#account-registration)
   - [Zero-knowledge proof for registration](2.md#protocol)

3. **[Asset Minting](3.md)**
   - [Issuer minting assets](3.md#asset-minting)
   - [Account state transitions](3.md#protocol)

4. **[Settlements](4.md)**
   - [Leg creation and encryption](4.md#leg)
   - [Settlement proof system](4.md#leg-creation-proof)

5. **[Sender/Receiver Affirmations](5.md)**
   - [Account state transition proofs](5.md#affirmations)
   - [Balance and counter updates](5.md#protocol)

6. **[Fee](6.md)**
   - [Fee account registration](6.md#account-registration)
   - [Fee account top-up](6.md#account-top-up)
   - [Fee payment](6.md#fee-payment)

**[Appendix](appendix.md)**

## Implementation

This mathematical specification is implemented in Rust using the Bulletproofs zero-knowledge proof system. The implementation can be found in the [GitHub repository](https://github.com/PolymeshAssociation/polymesh-dart/tree/main/dart-bp).

## Reading the Math

All mathematical expressions use LaTeX notation and are rendered using KaTeX. The notation follows standard cryptographic conventions:

- $\mathbb{G}_p, \mathbb{G}_q$: Elliptic curve groups
- $\mathbb{Z}_p, \mathbb{Z}_q$: Corresponding scalar fields
- $G, H$: Group generators
- $\stackrel{?}{=}$: Equality check in verification equations

## Navigation

Use the links above to navigate through the documentation, or view the source files directly on [GitHub](https://github.com/PolymeshAssociation/polymesh-dart/tree/main/dart-bp/docs).