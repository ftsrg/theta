#!/bin/bash

SUBPROJECT=$1 # e.g., xcfa/xcfa-cli

workdir=$(dirname $(dirname $(realpath "$0")))
tempdir=$(mktemp -d)

cp $workdir/subprojects/"$SUBPROJECT"/build/libs/theta-*-all.jar $tempdir/theta.jar
cp $workdir/scripts/theta-start.sh $tempdir/
cp -r $workdir/lib $tempdir/
pushd $tempdir
zip $workdir/package.zip * -r
popd
rm -r $tempdir
