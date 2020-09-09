#!/bin/bash

set -Eeuxo pipefail

DOCKER_RUN_OPTIONS="-i"

# Only allocate tty if we detect one
if [ -t 0 ] && [ -t 1 ]; then
    DOCKER_RUN_OPTIONS="$DOCKER_RUN_OPTIONS -t"
fi

ABSPATH=$(realpath "$1")
DIR=$(dirname "$ABSPATH")
FILE=/host/$(basename "$ABSPATH")
shift

docker run "$DOCKER_RUN_OPTIONS" --mount type=bind,source="$DIR",target=/host theta-sts-cli:latest --model "$FILE" "$@"
