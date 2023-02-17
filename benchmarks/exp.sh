#!/bin/bash

for i in {1..100}; do
    echo $i
    time java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar $1 $i
    echo "======================="
done
