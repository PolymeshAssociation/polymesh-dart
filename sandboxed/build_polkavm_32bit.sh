#!/usr/bin/env bash

TARGET_JSON_PATH="$(polkatool get-target-json-path --bitness 32)"
echo "$TARGET_JSON_PATH"

elf_path="../target/riscv32emac-unknown-none-polkavm/release/polymesh_dart_sandboxed.elf"
output_path="polymesh-dart-sandboxed.polkavm"
rm $output_path $elf_path

echo "> Building: 'polymesh-dart-sandboxed' (-> $output_path)"

RUSTFLAGS="--remap-path-prefix=$(pwd)= --remap-path-prefix=$HOME=~" \
cargo build  \
    -Z build-std=core,alloc \
    --target $TARGET_JSON_PATH \
    --release --lib -p polymesh-dart-sandboxed

polkatool link \
    --run-only-if-newer -s $elf_path \
    -o $output_path

