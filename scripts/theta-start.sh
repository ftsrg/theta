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

check_java_version() {
    if ! java --version 2>/dev/null | grep -q "openjdk $JAVA_VERSION"; then
        export PATH="$(IFS=:; echo "${JAVA_FALLBACK_PATHS[*]}"):$PATH"
    fi
    if ! java --version 2>/dev/null | grep -q "openjdk $JAVA_VERSION"; then
        print_error "Could not set up openjdk-$JAVA_VERSION. Is the JRE/JDK installed?"
    fi
}

remove_property_arg() {
    # Returns: "<property> <filtered args...>"
    local args=()
    local skip_next=0
    local property=""

    for arg in "$@"; do
        if [[ $skip_next -eq 1 ]]; then
            property="$arg"
            skip_next=0
            continue
        fi
        if [[ "$arg" == "--property" ]]; then
            skip_next=1
            continue
        fi
        args+=("$arg")
    done

    echo "$property ${args[*]}"
}

transform_property_if_needed() {
    local property=$1
    local infile=$2

    echo "Checking if property '$property' needs transformation" >&2

    case "$(basename "$property")" in
        termination.prp)
            perform_spec_transformation "termination" "$property" "$infile"
            ;;
        no-overflow.prp)
            perform_spec_transformation "no-overflow" "$property" "$infile"
            ;;
        # valid-memcleanup.prp)
        #     perform_spec_transformation "memcleanup" "$property" "$infile"
        #     ;;
        # valid-memsafety.prp)
        #     perform_spec_transformation "memsafety" "$property" "$infile"
        #     ;;
        *)
            echo "$property"
            ;;
    esac
}

perform_spec_transformation() {
    local from_property=$1
    local property=$2
    local infile=$3

    local transformed_property
    transformed_property="$(dirname "$property")/unreach-call.prp"
    echo "Mapping property '$property' to '$transformed_property'" >&2

    python3 "$scriptdir/transver/transver.py" \
        --from-property "$from_property" \
        --to-property reachability \
        --algorithm InstrumentationOperator \
        "$infile"

    echo "$transformed_property"
}

run_theta() {
    local args=$1
    local infile=$2
    local property=$3

    echo LD_LIBRARY_PATH="$scriptdir/lib" java -Xss120m -Xmx14210m -jar "$scriptdir/theta.jar" \
        $args --input "$infile" --property "$property" --smt-home "$scriptdir/solvers"
    LD_LIBRARY_PATH="$scriptdir/lib" java -Xss120m -Xmx14210m -jar "$scriptdir/theta.jar" \
        $args --input "$infile" --property "$property" --smt-home "$scriptdir/solvers"
}

# ----------------------------------------
# Main script logic
# ----------------------------------------

# Handle --version
if [[ "${1:-}" == "--version" ]]; then
    LD_LIBRARY_PATH="$scriptdir/lib" java -Xss120m -Xmx14210m -jar "$scriptdir/theta.jar" --version \
        || echo "$VERIFIER_VERSION"
    exit 0
fi

check_java_version

# Extract property argument and remaining args
read -r property modified_args <<<"$(remove_property_arg "${@:2}")"

if [[ -z "$property" ]]; then
    print_error "Missing --property argument"
fi

echo "Verifying input '$input_file' with property '$property' using arguments '$modified_args'"

# Transform property if needed
transformed_property=$(transform_property_if_needed "$property" "$input_file")

if [[ "$transformed_property" != "$property" ]]; then
    modified_args="$modified_args --input-file-for-witness $input_file"
    input_file="output/$(basename $input_file)"
fi

# Run Theta
run_theta "$modified_args" "$input_file" "$transformed_property"

# Witness mapping note
case "$(basename "$property")" in
    termination.prp | no-overflow.prp)
        echo "Not yet mapping witnesses from '$transformed_property' to '$property', hoping for the best"
        ;;
esac
