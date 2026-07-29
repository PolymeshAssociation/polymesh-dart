#!/usr/bin/env bash
# Nitro bring-up (step 1: hardcoded key, no KMS). Run from the workspace root on the parent.
set -euo pipefail

IMAGE=dart-auth-enclave:latest
EIF=dart-auth-enclave.eif
CID=16
CPUS=2
MEM=1024   # MiB

# 1. Build the container image (static musl binary). Defaults to arm64 in the Dockerfile;
#    on an x86_64 parent add: --build-arg RUST_TARGET=x86_64-unknown-linux-musl
docker build -f dart-auth-enclave/Dockerfile -t "$IMAGE" .

# 2. Build the enclave image (EIF). This prints PCR0/PCR1/PCR2 — save PCR0; it goes into the
#    KMS key policy in step 2 (M3b), and it changes on every rebuild.
nitro-cli build-enclave --docker-uri "$IMAGE" --output-file "$EIF"

# 3. Run the enclave. --debug-mode lets `nitro-cli console` show the enclave's stderr
#    ("listening on vsock port 5005"). NOTE: debug mode ZEROES the runtime attestation PCRs,
#    so drop --debug-mode for the KMS phase (the real PCR0 is the one build-enclave printed above).
nitro-cli run-enclave \
  --eif-path "$EIF" \
  --cpu-count "$CPUS" \
  --memory "$MEM" \
  --enclave-cid "$CID" \
  --debug-mode

echo
echo "Enclave running on CID $CID. Next, on the parent:"
echo "  # see the enclave's log:"
echo "  nitro-cli console --enclave-id \$(nitro-cli describe-enclaves | jq -r '.[0].EnclaveID')"
echo "  # build + run the host against the enclave (heavy host_proofs build):"
echo "  cargo build --release -p dart-auth-host"
echo "  ./target/release/dart-auth-host $CID     # expect: PASS ... (cid $CID)"
echo
echo "Teardown:  nitro-cli terminate-enclave --all"
