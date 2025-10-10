#!/bin/sh
WASI_SDK_PATH="/opt/wasi-sdk"

#CC="${WASI_SDK_PATH}/bin/clang -D_WASI_EMULATED_PROCESS_CLOCKS -lwasi-emulated-process-clocks --sysroot=${WASI_SDK_PATH}/share/wasi-sysroot -msimd128" \
CC="${WASI_SDK_PATH}/bin/clang -D_WASI_EMULATED_PROCESS_CLOCKS -lwasi-emulated-process-clocks --sysroot=${WASI_SDK_PATH}/share/wasi-sysroot" \
	cargo build --target wasm32-wasip1 --profile wasm32-wasi \
	--no-default-features \
	--bin wasi-module

cp ./target/wasm32-wasip1/wasm32-wasi/wasi-module.wasm ./src/
