#!/bin/bash

# Generate a whitelist for all the crates
#
# Usage: script <crate/download/dir> <file/with/list/of/crates> [timeout-per-crate-in-seconds]

set -eo pipefail

info() { echo -e "[-] ($(date '+%Y-%m-%d %H:%M:%S')) ${*}"; }
error() { echo -e "[!] ($(date '+%Y-%m-%d %H:%M:%S')) ${*}"; }

info "=== Generation of whitelists ==="

# Get the directory in which this script is contained
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"

# Get the folder in which all the crates has been downloaded
CRATE_DOWNLOAD_DIR="$(realpath "$1")"
if [[ ! -d "$CRATE_DOWNLOAD_DIR/000_libc" ]]; then
	echo "It looks like CRATE_DOWNLOAD_DIR (first argument) is wrong: '$CRATE_DOWNLOAD_DIR'"
	exit 1
fi

# Get the file with the list of crates to compile
CRATES_LIST_PATH="$(realpath "$2")"
if [[ ! -r "$CRATES_LIST_PATH" ]]; then
	error "Could not read file '$CRATES_LIST_PATH' (second argument)"
	exit 1
fi

start_date="$(date '+%Y-%m-%d-%H%M%S')"
whitelist_report="$CRATE_DOWNLOAD_DIR/whitelist-report-$start_date.csv"
whitelist_report_final="$CRATE_DOWNLOAD_DIR/whitelist-report.csv"
echo "'Crate name', 'Successful whitelist', 'Items in whitelist'" > "$whitelist_report"
info "Report: '$whitelist_report'"

info "Generate whitelist for $(cat "$CRATES_LIST_PATH" | wc -l) crates"

cat "$CRATES_LIST_PATH" | while read crate_name; do
	info "=== Crate '$crate_name' ==="
	CRATE_DIR="$CRATE_DOWNLOAD_DIR/$crate_name"
	CRATE_ROOT="$CRATE_DIR/source"

	jq '.functions[] | .node_path' \
		"$CRATE_ROOT/prusti-filter-results.json" \
		> "$CRATE_DIR/procedures.csv" \
		|| true

	jq '.functions[] | select(.procedure.restrictions | length == 0) | .node_path' \
		"$CRATE_ROOT/prusti-filter-results.json" \
		> "$CRATE_DIR/supported-procedures.csv" \
		|| true

	jq '.functions[] | select(.procedure.restrictions | length == 0) | select(.procedure.interestings | any(. == "uses assertions")) | .node_path' \
		"$CRATE_ROOT/prusti-filter-results.json" \
		> "$CRATE_DIR/supported-procedures-with-assertions.csv" \
		|| true

	num_procedures="$(cat "$CRATE_DIR/procedures.csv" | wc -l)"
	num_supported_procedures="$(cat "$CRATE_DIR/supported-procedures.csv" | wc -l)"
	num_supported_procedures_with_panics="$(cat "$CRATE_DIR/supported-procedures-with-assertions.csv" | wc -l)"

	info "Number of procedures: $num_procedures"
	info "Number of supported procedures: $num_supported_procedures"
	info "Number of supported procedures with panics: $num_supported_procedures_with_panics"

	echo "'$crate_name', $num_procedures, $num_supported_procedures, $num_supported_procedures_with_panics" >> "$whitelist_report"
done

cp "$whitelist_report" "$whitelist_report_final"
