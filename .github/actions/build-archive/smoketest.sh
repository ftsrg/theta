#!/bin/bash

set -euo pipefail

cd $(dirname $0)

./theta-start.sh input.c --svcomp --portfolio STABLE --property unreach-call.prp 2>&1 | tee output.log

grep "SafetyResult Unsafe" output.log && ls witness.yml