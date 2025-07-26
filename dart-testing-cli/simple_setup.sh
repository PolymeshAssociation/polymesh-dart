#!/bin/bash

rm -f dart_test.db

function run() {
    echo "Running: $@"
    # Debug
    #cargo run -- "$@"
    # Release
    cargo run --quiet --release -- "$@"
}

run init

run create-signer issuer
run create-signer investor
run create-signer mediator

run create-account issuer-0
run create-account investor-0
run create-account mediator-0

run create-asset issuer mediator mediator

run register-account issuer-0 0
run register-account investor-0 0

run end-block

run mint-assets issuer-0 0 1000

run create-settlement test issuer-0:investor-0:0:500

run end-block

run sender-affirm issuer-0 0 0 0 500

run receiver-affirm investor-0 0 0 0 500

run mediator-affirm mediator 0 0 -a

run end-block

run receiver-claim investor-0 0 0

run end-block
