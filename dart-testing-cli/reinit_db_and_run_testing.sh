#!/bin/bash

rm -f dart_test.db

function run() {
    echo "Running: $@"
    # Debug
    #cargo run -- "$@"
    # Release
    /bin/time -f "time: user: %U, rea: %e" cargo run --quiet --release -- "$@" || exit 1
}

run init

run create-signer -n issuer1
run create-signer -n issuer2
run create-signer -n investor
run create-signer -n mediator
run create-signer -n auditor

run create-account -s issuer1-0
run create-account -s issuer2-0
run create-account -s investor-0
run create-account -s mediator-0
run create-account -s auditor-0

run create-asset -s issuer1 --type auditor --auditor auditor
#run create-asset -s issuer1 --type mediator --auditor mediator
run create-asset -s issuer1 --type mediator --auditor mediator
#ASSET=0
ASSET=1

run register-account -s issuer1-0 --asset $ASSET
run register-account -s issuer2-0 --asset $ASSET

#run register-account -s investor-0 --asset $ASSET
run register-account -w register-account-proof.dat -s investor-0 --asset $ASSET
run register-account -r register-account-proof.dat -s investor-0 --asset $ASSET

run end-block

#run mint-assets -s issuer1-0 --asset $ASSET --amount 1000
run mint-assets -w mint-asset-proof.dat -s issuer1-0 --asset $ASSET --amount 1000
run mint-assets -r mint-asset-proof.dat -s issuer1-0 --asset $ASSET --amount 1000

run end-block

### Test a rejected settlement.

#run create-settlement -v test_reject --leg issuer1-0:investor-0:$ASSET:500
run create-settlement -w create-settlement-one-leg-proof.dat -v test_reject --leg issuer1-0:investor-0:$ASSET:500
run create-settlement -r create-settlement-one-leg-proof.dat -v test_reject --leg issuer1-0:investor-0:$ASSET:500

# The sender & Receiver affirm.
run sender-affirm -s issuer1-0 --settlement 0 --leg 0 --asset $ASSET --amount 500
run receiver-affirm -s investor-0 --settlement 0 --leg 0 --asset $ASSET --amount 500

run end-block

# The mediator rejects
#run mediator-affirm -s mediator --settlement 0 --leg 0
run mediator-affirm -w mediator-reject-proof.dat -s mediator --settlement 0 --leg 0
run mediator-affirm -r mediator-reject-proof.dat -s mediator --settlement 0 --leg 0

# TODO:
#run receiver-counter-update -s investor-0 --settlement 0 --leg 0

#run sender-reversal -s issuer1-0 --settlement 0 --leg 0
run sender-reversal -w sender-reversal-proof.dat -s issuer1-0 --settlement 0 --leg 0
run sender-reversal -r sender-reversal-proof.dat -s issuer1-0 --settlement 0 --leg 0

run end-block

### Test an executed settlement.
#
run create-settlement -v test_accept --leg issuer1-0:investor-0:$ASSET:500

#run sender-affirm -s issuer1-0 --settlement 1 --leg 0 --asset $ASSET --amount 500
run sender-affirm -w sender-affirm-proof.dat -s issuer1-0 --settlement 1 --leg 0 --asset $ASSET --amount 500
run sender-affirm -r sender-affirm-proof.dat -s issuer1-0 --settlement 1 --leg 0 --asset $ASSET --amount 500

#run receiver-affirm -s investor-0 --settlement 1 --leg 0 --asset $ASSET --amount 500
run receiver-affirm -w receiver-affirm-proof.dat -s investor-0 --settlement 1 --leg 0 --asset $ASSET --amount 500
run receiver-affirm -r receiver-affirm-proof.dat -s investor-0 --settlement 1 --leg 0 --asset $ASSET --amount 500

run end-block

#run mediator-affirm -s mediator --settlement 1 --leg 0 --accept
run mediator-affirm -w mediator-affirm-proof.dat -s mediator --settlement 1 --leg 0 --accept
run mediator-affirm -r mediator-affirm-proof.dat -s mediator --settlement 1 --leg 0 --accept

#run receiver-claim -s investor-0 --settlement 1 --leg 0
run receiver-claim -w receiver-claim-proof.dat -s investor-0 --settlement 1 --leg 0
run receiver-claim -r receiver-claim-proof.dat -s investor-0 --settlement 1 --leg 0

#run sender-counter-update -s issuer1-0 --settlement 1 --leg 0
run sender-counter-update -w sender-counter-update-proof.dat -s issuer1-0 --settlement 1 --leg 0
run sender-counter-update -r sender-counter-update-proof.dat -s issuer1-0 --settlement 1 --leg 0

run end-block

echo "========================= Finished"
