#!/bin/bash

echo -e "\nH2" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar H2
echo -e "\nH2bug" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar H2bug
echo -e "\nBV 1" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar BV 1
echo -e "\nBV1bug" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar BV1bug
echo -e "\nBV 2" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar BV 2
echo -e "\nBV 3" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar BV 3
echo -e "\nBV 4" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar BV 4
echo -e "\nBV 5" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar BV 5
echo -e "\nBV 6" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar BV 6
echo -e "\nBV 7" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar BV 7
echo -e "\nGroverSingleComp 2" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverSingleComp 2
echo -e "\nGroverSingleComp 4" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverSingleComp 4
echo -e "\nGroverAllComp 2" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverAllComp 2
echo -e "\nGroverAllComp 4" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverAllComp 4
echo -e "\nGroverSingleIter 1" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverSingleIter 1
echo -e "\nGroverSingleIter 2" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverSingleIter 2
echo -e "\nGroverSingleIter 3" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverSingleIter 3
echo -e "\nGroverSingleIter 4" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverSingleIter 4
echo -e "\nGroverSingleIter 5" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverSingleIter 5
echo -e "\nGroverAllIter 1" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverAllIter 1
echo -e "\nGroverAllIter 2" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverAllIter 2
echo -e "\nGroverAllIter 3" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverAllIter 3
echo -e "\nGroverAllIter 4" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverAllIter 4
echo -e "\nGroverAllIter 5" && time taskset -c 0 java -cp ./target/scala-2.11/Princess-assembly-2022-11-03.jar GroverAllIter 5