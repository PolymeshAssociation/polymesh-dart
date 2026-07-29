# docker build -f dart-auth-enclave/Dockerfile -t dart-auth-enclave .
# Defaults to arm64. For x86_64:
# docker build --build-arg RUST_TARGET=x86_64-unknown-linux-musl -f dart-auth-enclave/Dockerfile -t dart-auth-enclave .
ARG RUST_TARGET=aarch64-unknown-linux-musl

FROM rust:1-bookworm AS build
ARG RUST_TARGET
RUN rustup target add ${RUST_TARGET}
WORKDIR /src
COPY . .
# Light sigma-only build (no bulletproofs); pure-Rust so the self-contained musl needs no C toolchain.
RUN cargo build --release --target ${RUST_TARGET} -p dart-auth-enclave

FROM scratch
ARG RUST_TARGET
COPY --from=build /src/target/${RUST_TARGET}/release/dart-auth-enclave /dart-auth-enclave
ENTRYPOINT ["/dart-auth-enclave"]
