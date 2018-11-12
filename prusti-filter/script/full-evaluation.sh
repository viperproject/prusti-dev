#!/bin/bash

# Run the full evaluation
#
# Usage: script <crate/download/dir> [timeout-per-crate-in-seconds]

set -uo pipefail

info() { echo -e "[-] ($(date '+%Y-%m-%d %H:%M:%S')) ${*}"; }
error() { echo -e "[!] ($(date '+%Y-%m-%d %H:%M:%S')) ${*}"; }

# Get the directory in which this script is contained
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"

# Get the folder in which all the crates has been downloaded
CRATE_DOWNLOAD_DIR="$(cd "${1:-.}" && pwd)"
cd "$CRATE_DOWNLOAD_DIR"

if [[ ! -d "$CRATE_DOWNLOAD_DIR/000_libc" ]]; then
	error "It looks like CRATE_DOWNLOAD_DIR is wrong: '$CRATE_DOWNLOAD_DIR'"
	exit 1
fi

# Timeout
TIMEOUT="${2:-900}"
info "Using TIMEOUT=$TIMEOUT seconds"

start_date="$(date '+%Y-%m-%d-%H%M%S')"
evaluation_log_file="$CRATE_DOWNLOAD_DIR/full-evaluation-log-$start_date.log"
evaluation_log_file_final="$CRATE_DOWNLOAD_DIR/full-evaluation-log.log"
info "Using evaluation_log_file='$evaluation_log_file'"

(
	"$DIR/compile-crates.sh" "$CRATE_DOWNLOAD_DIR" "$TIMEOUT"

	"$DIR/filter-crates.sh" "$CRATE_DOWNLOAD_DIR" "$CRATE_DOWNLOAD_DIR/supported-crates.csv" "$TIMEOUT"

	"$DIR/whitelist-crates.sh" "$CRATE_DOWNLOAD_DIR" "$CRATE_DOWNLOAD_DIR/supported-crates.csv"

	"$DIR/verify-crates-coarse-grained.sh" "$CRATE_DOWNLOAD_DIR" "$CRATE_DOWNLOAD_DIR/supported-crates.csv" \
		"supported-procedures.csv" "$TIMEOUT"

	PRUSTI_CHECK_PANICS=true PRUSTI_CHECK_BINARY_OPERATIONS=true \
	"$DIR/verify-crates-fine-grained.sh" "$CRATE_DOWNLOAD_DIR" "$CRATE_DOWNLOAD_DIR/supported-crates.csv" \
		"supported-procedures-with-assertions.csv" "$TIMEOUT"

) 2>&1 | tee "$evaluation_log_file"

cp "$evaluation_log_file" "$evaluation_log_file_final"
