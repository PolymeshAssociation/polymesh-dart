# P-DART Bulletproofs Documentation

This directory contains the technical specification for P-DART using Bulletproofs.

## Reading the Documentation

The documentation is available in multiple formats:

### Online HTML Documentation
- **Live Documentation**: [View on GitHub Pages](https://polymeshassociation.github.io/dart/)
- Interactive HTML with rendered LaTeX math via KaTeX
- Searchable and navigable

### PDF Download
- **PDF Specification**: [Download PDF](https://polymeshassociation.github.io/dart/dart-bp-specification.pdf)
- Complete specification in a single PDF file
- Suitable for offline reading and printing

## Documentation Structure

The documentation is organized into the following sections:

1. **[index.md](index.md)** - Overview and introduction
2. **[1.md](1.md)** - Notation, Prerequisites and System Model
3. **[2.md](2.md)** - Account Registration
4. **[3.md](3.md)** - Minting Transaction
5. **[4.md](4.md)** - Settlement Initialization
6. **[5.md](5.md)** - Settlement Affirmation
7. **[6.md](6.md)** - Fee Accounts
8. **[appendix.md](appendix.md)** - Appendices and additional information

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
# On Ubuntu/Debian
sudo apt-get update
sudo apt-get install -y pandoc texlive-xetex texlive-fonts-recommended texlive-plain-generic

# On macOS (requires Homebrew)
brew install pandoc
brew install --cask mactex-no-gui
# Or for full MacTeX: brew install --cask mactex

# On other systems, install:
# - Pandoc: https://pandoc.org/installing.html
# - TeX Live: https://www.tug.org/texlive/
```

### Build HTML Documentation

```bash
# From the project root
RUSTDOCFLAGS="--html-in-header dart-bp/docs/katex-header.html" cargo doc --no-deps -p dart-bp-docs --open
```

The `--open` flag will automatically open the documentation in your browser. Without it, you can find the generated docs at `target/doc/dart_bp_docs/index.html`.

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

1. **HTML with auto-reload**: Use `cargo watch` for automatic rebuilds:
   ```bash
   cargo install cargo-watch
   RUSTDOCFLAGS="--html-in-header dart-bp/docs/katex-header.html" cargo watch -x 'doc --no-deps -p dart-bp-docs'
   ```

2. **Serve locally**: Use any static file server:
   ```bash
   # Using Python
   cd target/doc
   python3 -m http.server 8000
   # Then visit http://localhost:8000
   
   # Using Node.js http-server
   npx http-server target/doc -p 8000
   ```

## LaTeX Math Formatting

The documentation uses LaTeX for mathematical notation. Key conventions:

- **Inline math**: Use `$...$` for inline equations
- **Display math**: Use `$$...$$` for block equations (on their own lines)
- **Identifiers with underscores**: Escape literal underscores with backslash
  - Constants: `$MAX\_BALANCE$`, `$CHUNK\_BITS$`
  - Variables with subscripts: Use regular underscore `$x_i$`, `$w_1$`

### Examples

```markdown
The maximum balance is $MAX\_BALANCE = 2^{48} - 1$.

For the commitment $C = r.G + \sum_{i=1}^n w_i.G_i$, we have:

$$
T = r_T.G + \sum_{i=1}^n w_{i,T}.G_i
$$
```

### Testing Your Changes

Before submitting changes:

1. **Build HTML locally** to check rendering:
   ```bash
   RUSTDOCFLAGS="--html-in-header dart-bp/docs/katex-header.html" cargo doc --no-deps -p dart-bp-docs --open
   ```

2. **Build PDF locally** to verify LaTeX compatibility:
   ```bash
   cd dart-bp/docs && ./build-pdf.sh
   ```

3. **Check for common issues**:
   - Stray dollar signs in display math
   - Unescaped underscores in literal identifiers
   - Unclosed math delimiters
   - Browser console warnings (with `strict: false`, these should be minimal)

## Technical Details

### Math Rendering

- **HTML**: Uses [KaTeX v0.16.9](https://katex.org/) for client-side rendering
- **PDF**: Uses XeLaTeX with amsmath package
- **Configuration**: KaTeX runs in non-strict mode (`strict: false`) to accept common LaTeX patterns

### Build System

- **HTML**: Rust's `rustdoc` with embedded markdown via `#![doc = include_str!()]`
- **PDF**: Pandoc with XeLaTeX engine
- **CI/CD**: GitHub Actions automatically builds and deploys both formats on push

## License

See the main repository LICENSE file.

## Support

For questions or issues related to the documentation:
- Open an issue in the [main repository](https://github.com/PolymeshAssociation/dart/issues)
- Tag with `documentation` label

---

**Note**: The documentation is written to be both human-readable in markdown and properly rendered as HTML/PDF with mathematical notation. When copying LaTeX to Overleaf or other LaTeX editors, the math should work correctly.
