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

# Viper and Z3
export VIPER_HOME="$DIR/../../../viper"
export Z3_PATH="$DIR/../../../z3/bin/z3"

if [ -z "$(ls -A "$VIPER_HOME/*.jar")" ]; then
	error "It looks like VIPER_HOME is wrong: '$VIPER_HOME'"
	exit 1
fi

if [ -x "$Z3_PATH" ]; then
	error "It looks like Z3_PATH is wrong: '$Z3_PATH'"
	exit 1
fi

start_date="$(date '+%Y-%m-%d-%H%M%S')"
evaluation_log_file="$CRATE_DOWNLOAD_DIR/fine-grained-evaluation-log-$start_date.log"
evaluation_log_file_final="$CRATE_DOWNLOAD_DIR/fine-grained-evaluation-log.log"
info "Using evaluation_log_file='$evaluation_log_file'"

(

	PRUSTI_CHECK_PANICS=true PRUSTI_CHECK_BINARY_OPERATIONS=true \
	"$DIR/verify-crates-fine-grained.sh" "$CRATE_DOWNLOAD_DIR" "$CRATE_DOWNLOAD_DIR/supported-crates.csv" \
		"supported-procedures-with-assertions.csv" "$((TIMEOUT * 2))"

) 2>&1 | tee "$evaluation_log_file"

cp "$evaluation_log_file" "$evaluation_log_file_final"
