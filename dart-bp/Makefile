.PHONY: doc doc-internal pdf

# Build public API documentation with KaTeX math rendering
# This generates HTML docs for GitHub Pages deployment
doc:
	cd .. && RUSTDOCFLAGS="--html-in-header dart-bp/docs/katex-header.html" cargo doc --no-deps -p polymesh-dart-bp

# Build complete documentation including private items
# Useful for internal development and understanding implementation details
doc-internal:
	cd .. && RUSTDOCFLAGS="--html-in-header dart-bp/docs/katex-header.html" cargo doc --no-deps -p polymesh-dart-bp --document-private-items

# Generate PDF specification from markdown files
# Requires pandoc and XeLaTeX to be installed
pdf:
	cd docs && ./build-pdf.sh
