#!/bin/bash

set -euo pipefail

info() { echo -e "[-] ${*}"; }
error() { echo -e "[!] ${*}"; }

# Get the directory in which this script is contained
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"

# Get the name of this script
SCRIPT_NAME="$(basename -s '.sh' "$0")"

# Get the root directory of the crate, which is the first argument or the current folder
CRATE_ROOT="$(cd "${1:-.}" && pwd)"
cd "$CRATE_ROOT"

if [[ ! -r "$CRATE_ROOT/source/Cargo.toml" ]]; then
	error "Path '$CRATE_ROOT/source' does not look like the source of a crate"
	exit 1
fi

log_file="${CRATE_ROOT}/${SCRIPT_NAME}.log"
crate_source_dir="${CRATE_ROOT}/source"
crate_name="$(basename "$CRATE_ROOT")"

(
	echo ""
	echo "===== Verify crate '$crate_name' ($(date '+%Y-%m-%d %H:%M:%S')) ====="
	echo ""
	SECONDS=0
	# Timeout of 1 hour (+5 min)
	timeout -k 300 3600 "$DIR/verify-supported.sh" "$crate_source_dir" 2>&1
	exit_status="$?"
	duration="$SECONDS"
	whitelist_items="$(grep '"' "$crate_source_dir/Prusti.toml" | wc -l)"
	echo "Exit status: $exit_status"
	echo "Duration: $duration seconds"
	echo "Items in whitelist: $whitelist_items"
	echo ""
	echo "Summary for crate '$crate_name': exit status $exit_status, $whitelist_items items, $duration seconds ($(date '+%Y-%m-%d %H:%M:%S'))"
) 2>&1 | tee "$log_file"
