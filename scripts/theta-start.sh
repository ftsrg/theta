#!/bin/bash
set -euo pipefail

scriptdir=$(dirname "$(realpath "$0")")
input_file=$1

export VERIFIER_NAME=TOOL_NAME
export VERIFIER_VERSION=TOOL_VERSION
MIN_JAVA_VERSION=21

# ----------------------------------------
# Helper functions
# ----------------------------------------

print_error() {
    echo "Error: $*" >&2
    exit 1
}

get_java_version() {
  local version_raw
  version_raw="$("$1" -version 2>&1 | head -n 1)"

  local version
  version=$(echo "$version_raw" | sed -E 's/.*"([0-9]+).*/\1/')

  echo "$version"
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

# The native executable when the archive ships one, otherwise the jar on a suitable JVM. Both take
# the same arguments, -X options included.
if [[ -x "$scriptdir/theta" ]]; then
    THETA=("$scriptdir/theta" -Xss120m -Xmx14210m)
elif [[ "${1:-}" == "--version" ]]; then
    THETA=(java -Xss120m -Xmx14210m -jar "$scriptdir/theta.jar")
else
    JAVA_BIN=$(find_suitable_java) || print_error "No suitable Java (>= $MIN_JAVA_VERSION) found."
    echo "Using Java: $JAVA_BIN (version $(get_java_version "$JAVA_BIN"))"
    THETA=("$JAVA_BIN" -Xss120m -Xmx14210m -jar "$scriptdir/theta.jar")
fi

if [[ "${1:-}" == "--version" ]]; then
    LD_LIBRARY_PATH="$scriptdir/lib" "${THETA[@]}" --version || echo "$VERIFIER_VERSION"
    exit 0
fi

echo "Verifying input '$input_file' using arguments '${@:2}'"

echo LD_LIBRARY_PATH="$scriptdir/lib" "${THETA[@]}" \
    "${@:2}" --input "$input_file" --smt-home "$scriptdir/solvers"

LD_LIBRARY_PATH="$scriptdir/lib" "${THETA[@]}" \
    "${@:2}" --input "$input_file" --smt-home "$scriptdir/solvers"