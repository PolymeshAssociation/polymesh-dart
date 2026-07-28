# Build context is the workspace root: docker build -f dart-auth-enclave/Dockerfile -t dart-auth-enclave .
FROM rust:1-bookworm AS build
RUN rustup target add x86_64-unknown-linux-musl
WORKDIR /src
COPY . .
RUN cargo build --release --target x86_64-unknown-linux-musl -p dart-auth-enclave

FROM scratch
COPY --from=build /src/target/x86_64-unknown-linux-musl/release/dart-auth-enclave /dart-auth-enclave
ENTRYPOINT ["/dart-auth-enclave"]
