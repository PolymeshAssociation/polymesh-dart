# P-DART Bulletproofs

This crate provides the Bulletproofs-based cryptographic specification for Polymesh Distributed Anonymous Regulated Transactions (P-DART).

## 📖 Documentation

### Online Resources

- **📘 HTML Documentation**: [polymeshassociation.github.io/dart/](https://polymeshassociation.github.io/polymesh-dart/)
- **📄 PDF Specification**: [dart-bp-specification.pdf](https://polymeshassociation.github.io/polymesh-dart/dart-bp-specification.pdf)
  
### Documentation Sections

1. Overview and Introduction
2. Notation, Prerequisites and System Model  
3. Account Registration
4. Minting Transaction
5. Settlement Initialization
6. Settlement Affirmation
7. Fee Accounts
8. Appendix

## 🛠️ Building Documentation Locally

### Prerequisites

**For HTML Documentation:**
```bash
# Requires Rust and Cargo
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

**For PDF Generation:**
```bash
# On macOS (requires Homebrew)
brew install pandoc
brew install --cask mactex-no-gui
```

See [`docs/README.md`](docs/README.md) for complete installation instructions.

### Build Commands

**HTML Documentation:**
```bash
# From the dart-bp directory
cd dart-bp
make doc

# To include private items (for development)
make doc-internal
```

**PDF Specification:**
```bash
# From the dart-bp directory
cd dart-bp
make pdf

# Output will be: docs/dart-bp-specification.pdf

```

## ⚙️ Feature Flags

The crate's default features are `std`, `asm`, `parallel` and `host_proofs`.

- `host_proofs` — Build the Bulletproofs/curve-tree backed host protocols: account registration, legs, fees, key management and the device auth-proof API. 
   Pulls in the `bulletproofs`, `curve_tree_relations`, `ark-ec-divisors`, `ark-dlog-gadget` and `ark-pallas` dependencies. Without this feature only the `bp` wire 
   types (`encode`, `split_types`) are compiled, which is the HSM/TEE/Ledger device build.

- `large_baby_steps` — Use a larger precomputed baby-step table for discrete-log (BSGS) solving (`MAX_NUM_BABY_STEPS = 2^21` instead of `2^17`). This speeds up balance/amount 
   discrete logs at the cost of more memory and precomputation time; it is the deployed setting.

- `build-tables` — Benchmark-only: precompute fixed-base MSM tables for the verifier's final multi-scalar multiplication. Enables `verify_tuples_with_tables` / `batch_verify_tuples_with_tables`, 
   which verify Bulletproofs tuples against the tables plus a batch-affine MSM over the proof-dependent points. Implies `host_proofs`. Not intended for production builds.

- `parallel` — Enable general-purpose parallel computation (Rayon) across proving and verification. Used to reseed RNGs per thread and to parallelize independent MSM/verification work.

- `verifier_parallel` — Turn on this feature for faster proof verification. Implies `parallel` and additionally enables verification-targeted parallelism knobs (`ark-ec/parallel`, `bulletproofs/parallel_full`, `curve_tree_relations/parallel_full`, `ark-ec-divisors/parallel`, `ark-dlog-gadget/parallel`).


## ⚠️ Testing-only Feature Flags

This crate includes a feature flag intended solely for negative testing of verifier robustness.

- `ignore_prover_input_sanitation`: disables various prover-side input checks/sanitation so tests can intentionally generate malformed or inconsistent prover data.
  - Purpose: ensure verifiers *reject* bad inputs cleanly (returning `Error::ProofVerificationError(...)`) rather than panicking.
  - Do **not** enable this feature in production builds. Release builds will fail to compile if this feature is enabled.

- `nightly_mocking_tests` used to mock objects for testing. Needs nightly compiler.

Example:
```bash
cargo +nightly nextest run -p polymesh-dart-bp --features ignore_prover_input_sanitation,nightly_mocking_tests input_sanitation_disabled mocking_tests
```

Or

```bash
cargo test -p polymesh-dart-bp --features ignore_prover_input_sanitation,nightly_mocking_tests input_sanitation_disabled mocking_tests
```

## 🔄 Continuous Integration

Documentation is automatically built and deployed via GitHub Actions:

- **Workflow**: `.github/workflows/deploy-docs.yml`
- **Triggers**: 
  - Push to `main` or `katex` branches (when `dart-bp/docs/**` or `dart-bp/src/**` changes)
  - Manual workflow dispatch
- **Outputs**:
  - HTML docs deployed to GitHub Pages
  - PDF specification deployed alongside HTML

## 📚 Additional Resources

- Full authoring guide: [`docs/README.md`](docs/README.md)
- P-DART paper: [assets.polymesh.network/P-DART-v1.pdf](https://assets.polymesh.network/P-DART-v1.pdf)
