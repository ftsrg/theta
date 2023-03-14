#!/bin/bash
scriptdir=$(dirname $(realpath "$0"))

JAVA_FALLBACK_PATH="/usr/lib/jvm/java-17/bin/java"
JAVA=$(java --version 2>&1 | grep "openjdk 17" >/dev/null && echo "java" || echo $JAVA_FALLBACK_PATH)
$JAVA --version >/dev/null || exit

input="$1"
output="$2/$(basename $1 smt2)out"

echo LD_LIBRARY_PATH=$scriptdir/../lib $JAVA -Dfile.encoding=UTF-8 -jar $scriptdir/../theta.jar --chc --chc-transformation FORWARD --input $1 --search BFS --prunestrategy LAZY --precgranularity GLOBAL --domain PRED_SPLIT --refinement BW_BIN_ITP --maxenum 1 --smt-home $scriptdir/../solvers --RESULT loglevel > "$output"
result=$(LD_LIBRARY_PATH=$scriptdir/../lib $JAVA -Dfile.encoding=UTF-8 -jar $scriptdir/../theta.jar --chc --chc-transformation FORWARD --input $1 --search BFS --prunestrategy LAZY --precgranularity GLOBAL --domain PRED_SPLIT --refinement BW_BIN_ITP --maxenum 1 --smt-home $scriptdir/../solvers --loglevel RESULT 2>&1 | tee -a "$output" | grep SafetyResult)

if [[ $result == *"Unsafe"* ]]; then
	echo "unsat"
elif [[ $result == *"Safe"* ]]; then
	echo "sat"
else
	echo "unknown"
fi
