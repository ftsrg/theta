#!/bin/bash
if [ $1 == "--version" ]; then
    echo "3.0.0-svcomp22-qr"
else
    echo java -Xss120m -Xmx14210m -jar theta.jar "${@:2}" --input $1
    java -Xss120m -Xmx14210m -jar theta.jar "${@:2}" --input $1
fi
