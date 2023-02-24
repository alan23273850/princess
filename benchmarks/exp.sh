#!/bin/bash

echo "=" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar H2
echo "=" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar H2bug
echo "=" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar BVTest 1
echo "=" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar BV1bug
echo "=" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar BVTest 2
echo "=" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar BVTest 3
echo "=" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar BVTest 4
echo "=" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverAllComp 2
echo "=" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverSingleComp 2
echo "=" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverSingleComp 4
echo "=" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverAllIter 1
echo "=" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverAllIter 2
echo "=" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverSingleIter 1
echo "=" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverSingleIter 2
echo "=" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverSingleIter 3