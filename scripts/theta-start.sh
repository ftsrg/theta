#!/bin/bash
if [ $1 == "--version" ]; then
    echo "3.0.0-svcomp22-qr"
else
    scriptdir=$(dirname $(realpath "$0"))
    echo LD_LIBRARY_PATH=$scriptdir/lib java -Xss120m -Xmx14210m -jar $scriptdir/theta.jar "${@:2}" --input $1 --smt-home $scriptdir/solvers
    LD_LIBRARY_PATH=$scriptdir/lib java -Xss120m -Xmx14210m -jar $scriptdir/theta.jar "${@:2}" --input $1 --smt-home $scriptdir/solvers
fi
