# P-DART Bulletproofs Documentation

This directory contains the technical specification for Polymesh Distributed Anonymous Regulated Transactions (P-DART) using Bulletproofs-based zero-knowledge proofs.

## Reading the Documentation

The documentation is available in multiple formats:

### Online HTML Documentation
- **Live Documentation**: [View on GitHub Pages](https://polymeshassociation.github.io/polymesh-dart/)

### PDF Download
- **PDF Specification**: [Download PDF](https://polymeshassociation.github.io/polymesh-dart/dart-bp-specification.pdf)
- Complete specification in a single PDF file

## Documentation Structure

The documentation is organized into the following sections:

1. **[1.md](1.md)** - Notation, Prerequisites and System Model
2. **[2.md](2.md)** - Account Registration
3. **[3.md](3.md)** - Minting Transaction
4. **[4.md](4.md)** - Settlement Creation
5. **[5.md](5.md)** - Settlement Affirmations
6. **[6.md](6.md)** - Fee Accounts
7. **[appendix.md](appendix.md)** - Appendix

## Building Documentation Locally

### Prerequisites

#### For HTML Documentation
```bash
# Install Rust and Cargo (if not already installed)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Navigate to the project root
cd /path/to/dart
```

#### For PDF Generation
```bash
# On macOS (requires Homebrew)
brew install pandoc
brew install --cask mactex
# Or for full MacTeX: brew install --cask mactex
```

### Build HTML Documentation

```bash
# From the project root
RUSTDOCFLAGS="--html-in-header dart-bp/docs/katex-header.html" cargo doc --no-deps -p dart-bp-docs --open
```

### Build PDF Documentation

```bash
# From the project root
cd dart-bp/docs
./build-pdf.sh

# The PDF will be generated as: dart-bp-specification.pdf
```

To generate the PDF in a different location:
```bash
./build-pdf.sh /path/to/output/directory
```

## Viewing During Development

For quick iteration during documentation development:

Use any static file server:
   ```bash
   # Using Python
   cd target/doc
   python3 -m http.server 8000
   # Then visit http://localhost:8000
   
   # Using Node.js http-server
   npx http-server target/doc -p 8000
   ```

### Testing Your Changes

Before submitting changes:

1. **Build HTML locally** to check rendering:
   ```bash
   RUSTDOCFLAGS="--html-in-header dart-bp/docs/katex-header.html" cargo doc --no-deps -p dart-bp-docs --open
   ```

2. **Build PDF locally** to verify LaTeX compatibility:
   ```bash
   ./build-pdf.sh
   ```

## Technical Details

### Math Rendering

- **HTML**: Uses [KaTeX](https://katex.org/) for client-side rendering
- **PDF**: Uses XeLaTeX with amsmath package
- **Configuration**: KaTeX runs in non-strict mode (`strict: false`) to accept common LaTeX patterns

### Build System

- **HTML**: Rust's `rustdoc` with embedded markdown via `#![doc = include_str!()]`
- **PDF**: Pandoc with XeLaTeX engine
- **CI/CD**: GitHub Actions automatically builds and deploys both formats on push
