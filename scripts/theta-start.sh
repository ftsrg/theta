#!/bin/bash
set -euo pipefail

scriptdir=$(dirname "$(realpath "$0")")
input_file=$1

export VERIFIER_NAME=TOOL_NAME
export VERIFIER_VERSION=TOOL_VERSION
export JAVA_VERSION=17

# Java fallback paths (for systems with different OpenJDK locations)
JAVA_FALLBACK_PATHS=(
    "/usr/lib/jvm/java-$JAVA_VERSION-openjdk-amd64/bin/"
    "/usr/lib/jvm/java-$JAVA_VERSION-openjdk/bin/"
    "/usr/lib/jvm/java-$JAVA_VERSION/bin/"
)

# ----------------------------------------
# Helper functions
# ----------------------------------------

print_error() {
    echo "Error: $*" >&2
    exit 1
}

# ----------------------------------------
# Main script logic
# ----------------------------------------

if [[ "${1:-}" == "--version" ]]; then
    LD_LIBRARY_PATH="$scriptdir/lib" java -Xss120m -Xmx14210m -jar "$scriptdir/theta.jar" --version \
        || echo "$VERIFIER_VERSION"
    exit 0
fi

if ! java --version 2>/dev/null | grep -q "openjdk $JAVA_VERSION"; then
    export PATH="$(IFS=:; echo "${JAVA_FALLBACK_PATHS[*]}"):$PATH"
fi
if ! java --version 2>/dev/null | grep -q "openjdk $JAVA_VERSION"; then
    print_error "Could not set up openjdk-$JAVA_VERSION. Is the JRE/JDK installed?"
fi

echo "Verifying input '$input_file' using arguments '${@:2}'"

echo LD_LIBRARY_PATH="$scriptdir/lib" java -Xss120m -Xmx14210m -jar "$scriptdir/theta.jar" \
    "${@:2}" --input "$input_file" --smt-home "$scriptdir/solvers"
LD_LIBRARY_PATH="$scriptdir/lib" java -Xss120m -Xmx14210m -jar "$scriptdir/theta.jar" \
    "${@:2}" --input "$input_file" --smt-home "$scriptdir/solvers"