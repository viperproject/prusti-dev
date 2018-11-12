#!/bin/bash

# Run cargo-clean, cargo-build on all the crates
#
# Usage: script <crate/download/dir> [timeout-per-crate-in-seconds]

set -eo pipefail

info() { echo -e "[-] ($(date '+%Y-%m-%d %H:%M:%S')) ${*}"; }
error() { echo -e "[!] ($(date '+%Y-%m-%d %H:%M:%S')) ${*}"; }

info "=== Compilation ==="

# Get the directory in which this script is contained
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"

# Get the folder in which all the crates has been downloaded
CRATE_DOWNLOAD_DIR="$(realpath "$1")"
if [[ ! -d "$CRATE_DOWNLOAD_DIR/000_libc" ]]; then
	echo "It looks like CRATE_DOWNLOAD_DIR (first argument) is wrong: '$CRATE_DOWNLOAD_DIR'"
	exit 1
fi

# Compilation timeout
COMPILATION_TIMEOUT="${2:-900}"
info "Using COMPILATION_TIMEOUT=$COMPILATION_TIMEOUT seconds"

start_date="$(date '+%Y-%m-%d-%H%M%S')"
compilation_report="$CRATE_DOWNLOAD_DIR/compilation-report-$start_date.csv"
supported_crates="$CRATE_DOWNLOAD_DIR/supported-crates-$start_date.csv"
compilation_report_final="$CRATE_DOWNLOAD_DIR/compilation-report.csv"
supported_crates_final="$CRATE_DOWNLOAD_DIR/supported-crates.csv"
echo "'Crate name', 'Successful cleanup', 'Successful compilation', 'Duration (s)', 'Exit status', 'Start', 'End'" > "$compilation_report"
info "Report: '$compilation_report'"

info "Run standard compilation"

# Make sure that the "standard" compilation uses the same compiler flags as Prusti uses
export RUSTFLAGS="-Zborrowck=mir -Zpolonius -Znll-facts"
export POLONIUS_ALGORITHM="Naive"
export RUST_BACKTRACE=1

export RUSTUP_TOOLCHAIN="$(cat "$DIR/../../rust-toolchain")"
info "Using RUSTUP_TOOLCHAIN=$RUSTUP_TOOLCHAIN"

ls -d "$CRATE_DOWNLOAD_DIR"/*/ | while read crate_path; do
	crate_name="$(basename "$crate_path")"
	info "=== Crate '$crate_name' ==="
	CRATE_ROOT="$CRATE_DOWNLOAD_DIR/$crate_name/source"
	cd "$CRATE_ROOT"

	start_crate="$(date '+%Y-%m-%d %H:%M:%S')"

	exit_status="0"
	cargo clean || exit_status="$?"
	if [[ "$exit_status" != "0" ]]; then
		end_crate="$(date '+%Y-%m-%d %H:%M:%S')"
		info "Cargo clean failed with exit status $exit_status"
		echo "'$crate_name', false, false, 0, $exit_status, '$start_crate', '$end_crate'" >> "$compilation_report"
		continue
	fi

	exit_status="0"
	SECONDS=0
	timeout -k 10 "$COMPILATION_TIMEOUT" cargo build || exit_status="$?"
	duration="$SECONDS"
	if [[ "$exit_status" == "0" ]]; then
		end_crate="$(date '+%Y-%m-%d %H:%M:%S')"
		info "Successful compilation"
		echo "'$crate_name', true, true, $duration, $exit_status, '$start_crate', '$end_crate'" >> "$compilation_report"
		echo "$crate_name" >> "$supported_crates"
	else
		end_crate="$(date '+%Y-%m-%d %H:%M:%S')"
		info "Cargo build failed with exit status $exit_status"
		echo "'$crate_name', true, false, $duration, $exit_status, '$start_crate', '$end_crate'" >> "$compilation_report"
	fi
done

cp "$compilation_report" "$compilation_report_final"
cp "$supported_crates" "$supported_crates_final"
