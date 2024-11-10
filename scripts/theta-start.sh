#!/bin/bash
set -e

scriptdir=$(dirname "$(realpath "$0")")
IN=$1

export VERIFIER_NAME=TOOL_NAME
export VERIFIER_VERSION=TOOL_VERSION

JAVA_VERSION=17
JAVA_FALLBACK_PATH="/usr/lib/jvm/java-$JAVA_VERSION-openjdk-amd64/bin/:/usr/lib/jvm/java-$JAVA_VERSION-openjdk/bin/:/usr/lib/jvm/java-$JAVA_VERSION/bin/"
grep -o "openjdk $JAVA_VERSION" <<< "$(java --version)" >/dev/null || export PATH="$JAVA_FALLBACK_PATH":$PATH
grep -o "openjdk $JAVA_VERSION" <<< "$(java --version)" >/dev/null || {
    echo "Could not set up openjdk-$JAVA_VERSION. Is the JRE/JDK installed?"
    exit 1
}

remove_property() {
    local args=()
    local skip=0
    for arg in "$@"; do
        if [ "$skip" -eq 1 ]; then
            echo "$arg" > .property
            skip=0
            continue
        fi
        if [ "$arg" == "--property" ]; then
            skip=1
            continue
        fi
        args+=("$arg")
    done
    echo "${args[@]}"
}

if [ "$1" == "--version" ]; then
    LD_LIBRARY_PATH=$scriptdir/lib java -Xss120m -Xmx14210m -jar "$scriptdir"/theta.jar --version
else
    modified_args=$(remove_property "${@:2}")
    property=$(cat .property && rm .property)
    echo "Verifying input '$IN' with property '$property' using arguments '$modified_args'"

    if [ "$(basename "$property")" == "termination.prp" ]; then
        transformed_property=$(dirname "$property")/unreach-call.prp
        echo "Mapping property '$property' to '$transformed_property'"
        "$scriptdir"/specification-transformation.bin --from-property termination --to-property reachability --algorithm InstrumentationOperator $IN
        "$scriptdir"/offset.sh "$IN" "output/transformed_program.c" > witness-mapping.yml
        IN="output/transformed_program.c"
    elif [ "$(basename "$property")" == "no-overflow.prp" ]; then
        transformed_property=$(dirname "$property")/unreach-call.prp
        echo "Mapping property '$property' to '$transformed_property'"
        "$scriptdir"/specification-transformation.bin --from-property no-overflow --to-property reachability --algorithm InstrumentationOperator $IN
        "$scriptdir"/offset.sh "$IN" "output/transformed_program.c" > witness-mapping.yml
        IN="output/transformed_program.c"
    else
        transformed_property="$property"
    fi

    echo LD_LIBRARY_PATH="$scriptdir"/lib java -Xss120m -Xmx14210m -jar "$scriptdir"/theta.jar $modified_args --input "$IN" --property "$transformed_property" --smt-home "$scriptdir"/solvers
    LD_LIBRARY_PATH="$scriptdir"/lib java -Xss120m -Xmx14210m -jar "$scriptdir"/theta.jar $modified_args --input "$IN" --property "$transformed_property" --smt-home "$scriptdir"/solvers

    if [ "$(basename "$property")" == "termination.prp" ]; then
        echo "Not yet mapping witnesses from '$transformed_property' to '$property', hoping for the best"
    elif [ "$(basename "$property")" == "no-overflow.prp" ]; then
        echo "Not yet mapping witnesses from '$transformed_property' to '$property', hoping for the best"
    fi
fi
