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
