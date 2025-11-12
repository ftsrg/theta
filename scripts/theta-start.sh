#!/bin/bash
set -euo pipefail

scriptdir=$(dirname "$(realpath "$0")")
input_file=$1

export VERIFIER_NAME=TOOL_NAME
export VERIFIER_VERSION=TOOL_VERSION
MIN_JAVA_VERSION=17

# ----------------------------------------
# Helper functions
# ----------------------------------------

print_error() {
    echo "Error: $*" >&2
    exit 1
}

get_java_version() {
    "$1" -version 2>&1 | awk -F[\".] '/version/ {print $2}'
}

find_suitable_java() {
    # Try java from PATH first
    if command -v java >/dev/null 2>&1; then
        local version
        version=$(get_java_version "$(command -v java)" || echo 0)
        if (( version >= MIN_JAVA_VERSION )); then
            echo "$(command -v java)"
            return 0
        fi
    fi

    # Try common JVM locations
    for javadir in /usr/lib/jvm/*; do
        if [[ -x "$javadir/bin/java" ]]; then
            local version
            version=$(get_java_version "$javadir/bin/java" || echo 0)
            if (( version >= MIN_JAVA_VERSION )); then
                echo "$javadir/bin/java"
                return 0
            fi
        fi
    done

    return 1
}

# ----------------------------------------
# Main script logic
# ----------------------------------------

if [[ "${1:-}" == "--version" ]]; then
    LD_LIBRARY_PATH="$scriptdir/lib" java -Xss120m -Xmx14210m -jar "$scriptdir/theta.jar" --version \
        || echo "$VERIFIER_VERSION"
    exit 0
fi

JAVA_BIN=$(find_suitable_java) || print_error "No suitable Java (>= $MIN_JAVA_VERSION) found."

echo "Using Java: $JAVA_BIN (version $(get_java_version "$JAVA_BIN"))"

echo "Verifying input '$input_file' using arguments '${@:2}'"

echo LD_LIBRARY_PATH="$scriptdir/lib" "$JAVA_BIN" -Xss120m -Xmx14210m -jar "$scriptdir/theta.jar" \
    "${@:2}" --input "$input_file" --smt-home "$scriptdir/solvers"

LD_LIBRARY_PATH="$scriptdir/lib" "$JAVA_BIN" -Xss120m -Xmx14210m -jar "$scriptdir/theta.jar" \
    "${@:2}" --input "$input_file" --smt-home "$scriptdir/solvers"