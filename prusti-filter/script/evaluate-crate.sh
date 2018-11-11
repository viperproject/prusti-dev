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
) | tee "$log_file"

EVALUATION_TIMEOUT="${EVALUATION_TIMEOUT:-900}"
OVERALL_EVALUATION_TIMEOUT="$(( EVALUATION_TIMEOUT * 10 ))"
info "Using EVALUATION_TIMEOUT=$EVALUATION_TIMEOUT seconds" | tee -a "$log_file"
info "Using OVERALL_EVALUATION_TIMEOUT=$OVERALL_EVALUATION_TIMEOUT seconds" | tee -a "$log_file"

(
	echo "{"
	echo "  \"crate_name\": \"$crate_name\","
	echo "  \"start_date\": \"$start_date\","
	echo "  \"in_progress\": true"
	echo "}"
) | tee "$report_file"

(
	# Timeout is OVERALL_EVALUATION_TIMEOUT seconds (+5 min)
	timeout -k 300 $OVERALL_EVALUATION_TIMEOUT "$DIR/verify-supported.sh" "$crate_source_dir"
) 2>&1 | tee -a "$log_file"

exit_status="$?"
end_date="$(date '+%Y-%m-%d %H:%M:%S')"
duration="$SECONDS"
whitelist_items="$( echo "$(egrep 'Number of supported procedures in crate: [0-9]+$' "$log_file" | tail -n 1 | cut -d ' ' -f 10)" | sed 's/^$/0/' )"
verified_items="$( (egrep 'Received [0-9]+ items to be verified' "$log_file" | cut -d ' ' -f 6 | sed 's/$/+/' | tr '\n' ' ' ; echo "0") | bc )"
successful_items="$( (egrep 'Successful verification of [0-9]+ items' "$log_file" | cut -d ' ' -f 4 | sed 's/$/+/' | tr '\n' ' ' ; echo "0") | bc )"

(
	echo "Exit status: $exit_status"
	echo "Duration: $duration seconds"
	echo "Items in whitelist: $whitelist_items"
	echo ""
	echo "Summary for crate '$crate_name': exit status $exit_status, $whitelist_items/$verified_items/$successful_items items (whitelisted/verified/successful), $duration seconds ($end_date)"
) | tee -a "$log_file"

(
	echo "{"
	echo "  \"crate_name\": \"$crate_name\","
	echo "  \"exit_status\": \"$exit_status\","
	echo "  \"duration\": \"$duration\","
	echo "  \"whitelist_items\": \"$whitelist_items\","
	echo "  \"verified_items\": \"$verified_items\","
	echo "  \"successful_items\": \"$successful_items\","
	echo "  \"start_date\": \"$start_date\","
	echo "  \"end_date\": \"$end_date\","
	echo "  \"in_progress\": false"
	echo "}"
) | tee "$report_file"
