#!/bin/bash
set -e

# Build PDF from markdown documentation
# Requires: pandoc, texlive-full (or texlive-latex-extra + texlive-fonts-recommended)

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUTPUT_DIR="${1:-$SCRIPT_DIR}"
OUTPUT_FILE="$OUTPUT_DIR/dart-bp-specification.pdf"

echo "Building DART Bulletproofs Specification PDF..."
echo "Output: $OUTPUT_FILE"

# Combine all markdown files in order
cat > "$SCRIPT_DIR/combined.md" << 'EOF'
---
title: "P-DART: Bulletproofs-based Anonymous Regulated Transactions"
subtitle: "Technical Specification"
author: "Polymesh Association"
date: \today
documentclass: article
geometry: margin=1in
fontsize: 11pt
urlcolor: blue
header-includes: |
  \usepackage{amsmath}
  \usepackage{amssymb}
  \usepackage{mathtools}
  \usepackage{algorithm}
  \usepackage{algpseudocode}
  \usepackage{hyperref}
  \usepackage{graphicx}
  \usepackage{fancyhdr}
  \pagestyle{fancy}
  \fancyhead[L]{DART Specification}
  \fancyhead[R]{\thepage}
  \fancyfoot[C]{}
---

\newpage
\tableofcontents
\newpage

EOF

# Append all markdown files in order
for file in index.md 1.md 2.md 3.md 4.md 5.md 6.md appendix.md; do
  if [ -f "$SCRIPT_DIR/$file" ]; then
    echo "" >> "$SCRIPT_DIR/combined.md"
    echo "<!-- Source: $file -->" >> "$SCRIPT_DIR/combined.md"
    echo "" >> "$SCRIPT_DIR/combined.md"
    
    # Add page break before each major section (except first)
    if [ "$file" != "index.md" ]; then
      echo '\newpage' >> "$SCRIPT_DIR/combined.md"
      echo "" >> "$SCRIPT_DIR/combined.md"
    fi
    
    cat "$SCRIPT_DIR/$file" >> "$SCRIPT_DIR/combined.md"
  else
    echo "Warning: $file not found, skipping"
  fi
done

# Convert to PDF using pandoc
echo "Converting to PDF..."
pandoc "$SCRIPT_DIR/combined.md" \
  -o "$OUTPUT_FILE" \
  --pdf-engine=xelatex \
  --toc \
  --toc-depth=3 \
  --number-sections \
  -V linkcolor:blue \
  -V geometry:a4paper \
  -V geometry:margin=1in

if [ $? -eq 0 ] && [ -f "$OUTPUT_FILE" ]; then
  echo "✓ PDF generated successfully: $OUTPUT_FILE"
  rm -f "$SCRIPT_DIR/combined.md"
  exit 0
else
  echo "✗ PDF generation failed."
  if [ -f "$SCRIPT_DIR/combined.md" ]; then
    echo "Combined markdown saved at: $SCRIPT_DIR/combined.md"
  fi
  exit 1
fi
