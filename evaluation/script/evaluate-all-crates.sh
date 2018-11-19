#!/bin/bash

set -uo pipefail

info() { echo -e "[-] ${*}"; }
error() { echo -e "[!] ${*}"; }

# Get the directory in which this script is contained
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"
SCRIPT_NAME="$(basename -s '.sh' "$0")"

# Get the folder in which all the crates has been downloaded
CRATE_DOWNLOAD_DIR="$(cd "${1:-.}" && pwd)"
cd "$CRATE_DOWNLOAD_DIR"

if [[ ! -d "$CRATE_DOWNLOAD_DIR/000_libc" ]]; then
	echo "It looks like CRATE_DOWNLOAD_DIR is wrong: '$CRATE_DOWNLOAD_DIR'"
	exit 1
fi

# Force exit on Ctrl-c
function list_descendants() {
	local children=$(ps -o pid= --ppid "$1")
	for pid in $children; do
		list_descendants "$pid"
	done
	echo "$children"
}
function ctrl_c() {
	info "Force exit. Kill all subprocesses..."
	pkill -P $$
	exit 2
}
trap ctrl_c INT

start_date="$(date '+%Y-%m-%d-%H%M%S')"
evaluation_log_file="$CRATE_DOWNLOAD_DIR/evaluation-log-${start_date}.log"
evaluation_report_file="$CRATE_DOWNLOAD_DIR/evaluation-report-${start_date}.log"
info "Using evaluation_log_file='$evaluation_log_file'"
info "Using evaluation_report_file='$evaluation_report_file'"

echo "=== Start evaluation $start_date ===" | tee "$evaluation_log_file"

# Run evaluations in parallel
MAX_PARALLEL_EVALUATIONS="${MAX_PARALLEL_EVALUATIONS:-1}"
info "Using MAX_PARALLEL_EVALUATIONS=$MAX_PARALLEL_EVALUATIONS" | tee -a "$evaluation_log_file"

ls -d "$CRATE_DOWNLOAD_DIR"/*/ | \
	xargs -I CMD --max-procs="$MAX_PARALLEL_EVALUATIONS" --max-args=1 \
	"$DIR/evaluate-crate.sh" CMD \
	2>&1 | tee -a "$evaluation_log_file"

# Analyze evaluation
"$DIR/analyze-evaluation.sh" "$CRATE_DOWNLOAD_DIR" \
	| tee "$evaluation_report_file" \
	| tee -a "$evaluation_log_file"
