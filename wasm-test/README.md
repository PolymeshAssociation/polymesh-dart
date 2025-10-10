# wasi-test-sandboxed

## Build

The `./src/wasi-module.wasm` file can be rebuild by running `./rebuild-wasi-app.sh`.

Requires [wasi-sdk](https://github.com/WebAssembly/wasi-sdk).

## Run

```bash
# Runs in both WASM32 (sandboxed) and Native (most likely 64-bit)
cargo run --release

# Install the i686 target (linux)
rustup target add i686-unknown-linux-gnu

# Run only 32-bit native.
cargo run --release --no-default-features --target i686-unknown-linux-gnu
```
