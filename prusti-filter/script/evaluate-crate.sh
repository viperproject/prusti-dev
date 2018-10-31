#!/bin/bash

set -uo pipefail

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
report_file="${CRATE_ROOT}/report.json"
crate_source_dir="${CRATE_ROOT}/source"
crate_name="$(basename "$CRATE_ROOT")"

start_date="$(date '+%Y-%m-%d %H:%M:%S')"
SECONDS=0

(
	echo ""
	echo "===== Verify crate '$crate_name' ($start_date) ====="
	echo ""
	# Timeout of 1 hour (+5 min)
	timeout -k 300 3600 "$DIR/verify-supported.sh" "$crate_source_dir" 2>&1
) 2>&1 | tee "$log_file"

exit_status="$?"
end_date="$(date '+%Y-%m-%d %H:%M:%S')"
duration="$SECONDS"
whitelist_items="$(grep '"' "$crate_source_dir/Prusti.toml" | wc -l)"
verified_items="$(egrep 'Received [0-9]+ items to be verified' "$log_file" | tail -n 1 | cut -d ' ' -f 6)"

(
	echo "Exit status: $exit_status"
	echo "Duration: $duration seconds"
	echo "Items in whitelist: $whitelist_items"
	echo ""
	echo "Summary for crate '$crate_name': exit status $exit_status, $verified_items verified items (of $whitelist_items in the whitelist), $duration seconds ($end_date)"
) 2>&1 | tee -a "$log_file"

(
	echo "{"
	echo "  'crate_name': '$crate_name',"
	echo "  'exit_status': '$exit_status',"
	echo "  'duration': '$duration',"
	echo "  'whitelist_items': '$whitelist_items',"
	echo "  'verified_items': '$verified_items',"
	echo "  'start_date': '$start_date',"
	echo "  'end_date': '$end_date'"
	echo "}"
) | tee "$report_file"
