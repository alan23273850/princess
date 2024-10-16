#!/bin/bash

# for n in {95..99}; do
#     echo "Running BVsingleBug on circuit $n"
#     timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar BVsingleBug ~/AutoQ/POPL25/Evaluation/non-parameterized/missgate/BV/$n/circuit.qasm
# done

# for n in {09..13}; do
#     echo "Running BVallBug on circuit $n"
#     timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar BVallBug ~/AutoQ/POPL25/Evaluation/non-parameterized/missgate/MOBV_reorder/$n/circuit.qasm
# done

# echo "Running GHZsingleBug on circuit 064"
# timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar GHZsingleBug ~/AutoQ/POPL25/Evaluation/non-parameterized/missgate/GHZzero/064/circuit.qasm
# for (( n=128; n<=512; n=n+128 )); do
#     echo "Running GHZsingleBug on circuit $n"
#     timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar GHZsingleBug ~/AutoQ/POPL25/Evaluation/non-parameterized/missgate/GHZzero/$n/circuit.qasm
# done

# for (( n=8; n<=128; n=n*2 )); do
#     echo "Running GHZallBug on circuit $n"
#     timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar GHZallBug ~/AutoQ/POPL25/Evaluation/non-parameterized/missgate/GHZall/$(printf "%03d" $n)/circuit.qasm
# done

# for (( n=12; n<=20; n=n+2 )); do
#     echo "Running GroverSingleBug on circuit $n"
#     timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar GroverSingleBug ~/AutoQ/POPL25/Evaluation/non-parameterized/missgate/Grover/$n/circuit.qasm
# done

# for (( n=6; n<=10; n=n+1 )); do
#     echo "Running GroverAllBug on circuit $n"
#     timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar GroverAllBug ~/AutoQ/POPL25/Evaluation/non-parameterized/missgate/MOGrover/$(printf "%02d" $n)/circuit.qasm
# done

# for n in 012 013 064 128 256; do
#     echo "Running H2allBug on circuit $n"
#     timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar H2allBug ~/AutoQ/POPL25/Evaluation/non-parameterized/missgate/H2/$n/circuit.qasm
# done

# for n in 10 11 12 13 99; do
#     echo "Running HXHallBug on circuit $n"
#     timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar HXHallBug ~/AutoQ/POPL25/Evaluation/non-parameterized/missgate/HXH/$n/circuit.qasm
# done

# for (( n=8; n<=16; n=n+2 )); do
#     echo "Running MCXallBug on circuit $n"
#     timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar MCXallBug ~/AutoQ/POPL25/Evaluation/non-parameterized/missgate/MCToffoli/$(printf "%02d" $n)/circuit.qasm
# done

for n in 02 18 50 75 100; do
    echo "Running OEGrover on circuit $n"
    timeout 300 time java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar OEGroverBug ~/AutoQ/POPL25/Evaluation/non-parameterized/missgate/OEGrover/$n/circuit.qasm
done
