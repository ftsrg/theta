#!/bin/bash
set -e

scriptdir=$(dirname "$(realpath "$0")")
IN=$1

export VERIFIER_NAME=TOOL_NAME
export VERIFIER_VERSION=TOOL_VERSION

if [ "$1" == "--version" ]; then
    LD_LIBRARY_PATH=$scriptdir/lib java -Xss120m -Xmx14210m -jar "$scriptdir"/theta.jar --version || echo $VERIFIER_VERSION
    exit
fi

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

modified_args=$(remove_property "${@:2}")
property=$(cat .property && rm .property)
echo "Verifying input '$IN' with property '$property' using arguments '$modified_args'"

if [ "$(basename "$property")" == "no-overflow.prp" ]; then
    transformed_property=$(dirname "$property")/unreach-call.prp
    echo "Mapping property '$property' to '$transformed_property'"
    TMPFILE=$(mktemp -p $PWD)
    sed 's/__VERIFIER_assert/__OLD_VERIFIER_assert/g;s/reach_error/old_reach_error/g' "$IN" > "$TMPFILE"
    python3 "$scriptdir"/specification-transformation/src/specification-transformation.py --from-property no-overflow --to-property reachability --algorithm InstrumentationOperator "$TMPFILE"
    #"$scriptdir"/offset.sh "$IN" "output/transformed_program.c" > witness-mapping.yml
    modified_args="$modified_args --input-file-for-witness $IN"
    IN="output/transformed_program.c"
    rm "$TMPFILE"
else
    transformed_property="$property"
fi

echo LD_LIBRARY_PATH="$scriptdir"/lib java -Xss120m -Xmx14210m -jar "$scriptdir"/theta.jar $modified_args --input "$IN" --property "$transformed_property" --smt-home "$scriptdir"/solvers
LD_LIBRARY_PATH="$scriptdir"/lib java -Xss120m -Xmx14210m -jar "$scriptdir"/theta.jar $modified_args --input "$IN" --property "$transformed_property" --smt-home "$scriptdir"/solvers

if [ "$(basename "$property")" == "no-overflow.prp" ]; then
    echo "Not yet mapping witnesses from '$transformed_property' to '$property', hoping for the best"
fi
