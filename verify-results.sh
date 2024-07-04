#!/bin/bash

if command -v python3 &>/dev/null; then
    PYTHON=python3
else
    PYTHON=python
fi

examples=(
    "TreeTermination"
    "EchoMachine_round"
    "EchoMachine_value"
    "ToyConsensus_value"
    "ToyConsensus_quorum"
    "ToyConsensus_node"
    "LockServer"
    "ListToken"
    "PlusMinus"
    "EqualSum_thread"
    "EqualSum_index"
    "EqualSumOrders_thread"
    "EqualSumOrders_index"
)

for example in "${examples[@]}"; do
    echo -n "verifying $example ... "
    $PYTHON src/mypyvy.py verify-cutoff examples/cutoffs/$example.pyv | grep -e "all ok!" -e "failed!"
done
