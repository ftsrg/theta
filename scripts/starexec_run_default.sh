#!/bin/bash
scriptdir=$(dirname $(realpath "$0"))

JAVA_FALLBACK_PATH="/usr/lib/jvm/java-17/bin/java"
JAVA=$(java --version 2>&1 | grep "openjdk 17" >/dev/null && echo "java" || echo $JAVA_FALLBACK_PATH)
$JAVA --version >/dev/null || exit

input="$1"
output="$2/$(basename $1 smt2)out"

configurations=("--domain PRED_SPLIT --refinement BW_BIN_ITP --predsplit WHOLE"
				"--domain PRED_CART --refinement BW_BIN_ITP --predsplit WHOLE"
				"--domain EXPL --refinement SEQ_ITP")

SECONDS=0

for i in ${!configurations[@]}; do
    flags=${configurations[$i]}
    remaining=$(((1800-$SECONDS)/(3-i)))
    echo "Running config ($i) for $remaining seconds..." >> "$output"
    echo LD_LIBRARY_PATH=$scriptdir/../lib $JAVA -Xss120m -Xmx28G -Dfile.encoding=UTF-8 -jar $scriptdir/../theta.jar --chc --input $1 $flags --maxenum 1 --initprec EMPTY --smt-home $scriptdir/../solvers --loglevel RESULT >> "$output"
	result=$(LD_LIBRARY_PATH=$scriptdir/../lib timeout $remaining $JAVA -Xss120m -Xmx28G -Dfile.encoding=UTF-8 -jar $scriptdir/../theta.jar --chc --input $1 $flags --maxenum 1 --initprec EMPTY --smt-home $scriptdir/../solvers --loglevel RESULT 2>&1 | tee -a "$output" | grep SafetyResult)

	if [[ $result == *"Unsafe"* ]]; then
		echo "unsat"
		exit
	elif [[ $result == *"Safe"* ]]; then
		echo "sat"
		exit
	fi
done

echo "unknown"
