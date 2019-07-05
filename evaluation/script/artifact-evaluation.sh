#!/bin/bash

set -uo pipefail

# Get the directory in which this script is contained
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"

CRATES_DIR="$DIR/../../../crates"
VIPER_DIR="$DIR/../../../viper"
Z3_EXE="$DIR/../../../z3/bin/z3"

mkdir -p "$CRATES_DIR"

"$DIR/download-top-500.sh" "$CRATES_DIR"

"$DIR/set-cargo-lock.sh" "$CRATES_DIR"

ln -s /usr/lib/viper "$VIPER_DIR"
mkdir -p "$(dirname "$Z3_EXE")"
ln -s /usr/local/bin/z3 "$Z3_EXE"

"$DIR/full-evaluation.sh" "$CRATES_DIR"
