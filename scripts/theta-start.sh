#!/bin/bash
scriptdir=$(dirname $(realpath "$0"))

JAVA_FALLBACK_PATH="/usr/lib/jvm/java-17-openjdk-amd64/bin/java"
JAVA=$(java --version | grep "openjdk 17" >/dev/null && echo "java" || echo $JAVA_FALLBACK_PATH)
$JAVA --version >/dev/null || exit

if [ $1 == "--version" ]; then
    # echo LD_LIBRARY_PATH=$scriptdir/lib $JAVA -Xss120m -Xmx14210m -jar $scriptdir/theta.jar --version
    LD_LIBRARY_PATH=$scriptdir/lib $JAVA -Xss120m -Xmx14210m -jar $scriptdir/theta.jar --version
else
    echo LD_LIBRARY_PATH=$scriptdir/lib $JAVA -Xss120m -Xmx14210m -jar $scriptdir/theta.jar "${@:2}" --input $1 --smt-home $scriptdir/solvers
    LD_LIBRARY_PATH=$scriptdir/lib $JAVA -Xss120m -Xmx14210m -jar $scriptdir/theta.jar "${@:2}" --input $1 --smt-home $scriptdir/solvers
fi
