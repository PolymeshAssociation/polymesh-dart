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

run create-signer -n issuer
run create-signer -n investor
run create-signer -n mediator

run create-account -s issuer-0
run create-account -s investor-0
run create-account -s mediator-0

run create-asset -s issuer --type mediator --auditor mediator

run register-account -s issuer-0 --asset 0
run register-account -s investor-0 --asset 0

run end-block

run mint-assets -s issuer-0 --asset 0 --amount 1000

run create-settlement -v test --leg issuer-0:investor-0:0:500

run end-block

#run sender-affirm -s issuer-0 --settlement 0 --leg 0 --asset 0 --amount 500
run sender-affirm -w sender-affirm-proof.dat -s issuer-0 --settlement 0 --leg 0 --asset 0 --amount 500
run sender-affirm -r sender-affirm-proof.dat -s issuer-0 --settlement 0 --leg 0 --asset 0 --amount 500

#run receiver-affirm -s investor-0 --settlement 0 --leg 0 --asset 0 --amount 500
run receiver-affirm -w receiver-affirm-proof.dat -s investor-0 --settlement 0 --leg 0 --asset 0 --amount 500
run receiver-affirm -r receiver-affirm-proof.dat -s investor-0 --settlement 0 --leg 0 --asset 0 --amount 500

run mediator-affirm -s mediator --settlement 0 --leg 0 --accept

run end-block

run receiver-claim -s investor-0 --settlement 0 --leg 0

run end-block
