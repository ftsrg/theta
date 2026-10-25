#!/bin/bash
set -euo pipefail

scriptdir=$(dirname "$(realpath "$0")")
input_file=$1

export VERIFIER_NAME=TOOL_NAME
export VERIFIER_VERSION=TOOL_VERSION

if [[ "${1:-}" == "--version" ]]; then
    LD_LIBRARY_PATH="$scriptdir/lib" "$scriptdir/theta" --version || echo "$VERIFIER_VERSION"
    exit 0
fi

echo "Verifying input '$input_file' using arguments '${@:2}'"

echo LD_LIBRARY_PATH="$scriptdir/lib" "$scriptdir/theta" -Xss120m -Xmx14210m \
    "${@:2}" --input "$input_file" --smt-home "$scriptdir/solvers"

LD_LIBRARY_PATH="$scriptdir/lib" "$scriptdir/theta" -Xss120m -Xmx14210m \
    "${@:2}" --input "$input_file" --smt-home "$scriptdir/solvers"
