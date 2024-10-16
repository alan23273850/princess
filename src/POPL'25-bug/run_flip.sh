#!/bin/bash

# for n in {95..99}; do
#     echo "Running BVsingle on circuit $n"
#     timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar BVsingleBug ~/AutoQ/POPL25/Evaluation/non-parameterized/flipgate/BV/$n/circuit.qasm
# done

# echo "Running GHZsingle on circuit 064"
# timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar GHZsingleBug ~/AutoQ/POPL25/Evaluation/non-parameterized/flipgate/GHZzero/064/circuit.qasm
# for (( n=128; n<=512; n=n+128 )); do
#     echo "Running GHZsingle on circuit $n"
#     timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar GHZsingleBug ~/AutoQ/POPL25/Evaluation/non-parameterized/flipgate/GHZzero/$n/circuit.qasm
# done

for (( n=8; n<=128; n=n*2 )); do
    echo "Running GHZall on circuit $n"
    timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar GHZallBug ~/AutoQ/POPL25/Evaluation/non-parameterized/flipgate/GHZall/$(printf "%03d" $n)/circuit.qasm
done

# for (( n=12; n<=20; n=n+2 )); do
#     echo "Running GroverSingle on circuit $n"
#     timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar GroverSingleBug ~/AutoQ/POPL25/Evaluation/non-parameterized/flipgate/Grover/$n/circuit.qasm
# done

# for (( n=6; n<=10; n=n+1 )); do
#     echo "Running GroverAll on circuit $n"
#     timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar GroverAllBug ~/AutoQ/POPL25/Evaluation/non-parameterized/flipgate/MOGrover/$(printf "%02d" $n)/circuit.qasm
# done

# for (( n=8; n<=16; n=n+2 )); do
#     echo "Running MCXall on circuit $n"
#     timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar MCXallBug ~/AutoQ/POPL25/Evaluation/non-parameterized/flipgate/MCToffoli/$(printf "%02d" $n)/circuit.qasm
# done
