#!/bin/bash

set -uo pipefail

# Get the directory in which this script is contained
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"

if [[ ! -d "$1" ]]; then
	echo "It looks like ARTEFACT_DIR (the first argument) is not a valid path: '$1'"
	exit 1
fi

# Get the folder in which to prepare the artefact files
ARTEFACT_DIR="$(cd "${1:-.}" && pwd)"

if [[ ! -z "$(ls -A "$ARTEFACT_DIR")" ]]; then
	echo "It looks like ARTEFACT_DIR (the first argument) is not an empty folder: '$ARTEFACT_DIR'"
	exit 1
fi

mkdir "$ARTEFACT_DIR/top-500"
mkdir "$ARTEFACT_DIR/evaluation-1"
mkdir "$ARTEFACT_DIR/evaluation-2"
mkdir "$ARTEFACT_DIR/evaluation-3"
mkdir "$ARTEFACT_DIR/evaluation-3/originals"
mkdir "$ARTEFACT_DIR/evaluation-3/with-overflow-checks"
mkdir "$ARTEFACT_DIR/evaluation-3/without-overflow-checks"

. $DIR/download-top-500.sh "$ARTEFACT_DIR/top-500"
. $DIR/set-cargo-lock.sh "$ARTEFACT_DIR/top-500"

########## evaluation 1 ##########

cat "$DIR/../crates/supported-crates.csv" | while read crate
do
    echo === $crate ===
    cp -r "$ARTEFACT_DIR/top-500/$crate/source" "$ARTEFACT_DIR/evaluation-1/$crate"
    cp "$DIR/../crates/coarse-grained-config/$crate.Prusti.toml" "$ARTEFACT_DIR/evaluation-1/$crate/Prusti.toml"
done

########## evaluation 2 ##########

(cd "$DIR/../crates/fine-grained-config"; ls) | while read config_file
do
    crate=$(echo $config_file | cut -d. -f1)
    num=$(echo $config_file | cut -d. -f2)
    echo === $crate $num ===
    cp -r "$ARTEFACT_DIR/top-500/$crate/source" "$ARTEFACT_DIR/evaluation-2/${crate}_${num}"
    cp "$DIR/../crates/fine-grained-config/$config_file" "$ARTEFACT_DIR/evaluation-2/${crate}_${num}/Prusti.toml"
done

########## evaluation 3 ##########

cp -r "$DIR/../artifact/examples/"*.orig "$ARTEFACT_DIR/evaluation-3/originals"

cat "$DIR/../benchmark/benchmark.py" | grep "prusti/tests/verify" | grep -v "overflow" | while read file
do
    echo === $file ===
    cp -r "$DIR/../../$file" "$ARTEFACT_DIR/evaluation-3/without-overflow-checks/"
done

cat "$DIR/../benchmark/benchmark.py" | grep "prusti/tests/verify" | grep "overflow" | while read file
do
    echo === $file ===
    cp -r "$DIR/../../$file" "$ARTEFACT_DIR/evaluation-3/with-overflow-checks/"
done

echo "CHECK_BINARY_OPERATIONS = true" > "$ARTEFACT_DIR/evaluation-3/with-overflow-checks/Prusti.toml"
