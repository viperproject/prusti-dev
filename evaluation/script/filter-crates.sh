#!/bin/bash

# Run cargo-prusti-filter on all the crates
#
# Usage: script <crate/download/dir> <file/with/list/of/crates> [timeout-per-crate-in-seconds]

set -eo pipefail

info() { echo -e "[-] ($(date '+%Y-%m-%d %H:%M:%S')) ${*}"; }
error() { echo -e "[!] ($(date '+%Y-%m-%d %H:%M:%S')) ${*}"; }

cargoclean() {
	# Clean the artifacts of this project ("bin" or "lib"), but not those of the dependencies
	names="$(cargo metadata --format-version 1 | jq -r '.packages[].targets[] | select( .kind | map(. == "bin" or . == "lib") | any ) | select ( .src_path | contains(".cargo/registry") | . != true ) | .name')"
	for name in $names; do
		cargo clean -p "$name" || cargo clean
	done
}

info "=== Filtering ==="

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

# Compilation timeout
FILTERING_TIMEOUT="${3:-900}"
info "Using FILTERING_TIMEOUT=$FILTERING_TIMEOUT seconds"

CARGO_PRUSTI_FILTER="$DIR/../../docker/cargo-prusti-filter"
info "Using CARGO_PRUSTI_FILTER=$CARGO_PRUSTI_FILTER"

start_date="$(date '+%Y-%m-%d-%H%M%S')"
filtering_report="$CRATE_DOWNLOAD_DIR/filtering-report-$start_date.csv"
filtering_report_final="$CRATE_DOWNLOAD_DIR/filtering-report.csv"
echo "Crate name,Successful filtering,Duration (s),Exit status,Start,End" > "$filtering_report"
info "Report: '$filtering_report'"

info "Run filtering on $(cat "$CRATES_LIST_PATH" | wc -l) crates"

# Make sure that the "standard" compilation uses the same compiler flags as Prusti uses
export RUSTFLAGS="-Zborrowck=mir -Zpolonius -Znll-facts" # "-C overflow-check=yes"
export POLONIUS_ALGORITHM="Naive"
export RUST_BACKTRACE=1

export RUSTUP_TOOLCHAIN="$(cat "$DIR/../../rust-toolchain")"
info "Using RUSTUP_TOOLCHAIN=$RUSTUP_TOOLCHAIN"

cat "$CRATES_LIST_PATH" | while read crate_name; do
	info "=== Crate '$crate_name' ==="
	CRATE_ROOT="$CRATE_DOWNLOAD_DIR/$crate_name/source"
	cd "$CRATE_ROOT"

	start_crate="$(date '+%Y-%m-%d %H:%M:%S')"

	rm -f "$CRATE_ROOT/prusti-filter-results.json"
	cargoclean

	exit_status="0"
	SECONDS=0
	timeout -k 10 "$FILTERING_TIMEOUT" "$CARGO_PRUSTI_FILTER" -j 1 || exit_status="$?"
	duration="$SECONDS"
	if [[ "$exit_status" == "0" ]]; then
		end_crate="$(date '+%Y-%m-%d %H:%M:%S')"
		info "Successful filtering"
		echo "$crate_name,true,$duration,$exit_status,$start_crate,$end_crate" >> "$filtering_report"
	else
		end_crate="$(date '+%Y-%m-%d %H:%M:%S')"
		info "Filtering failed with exit status $exit_status."
		echo "$crate_name,false,$duration,$exit_status,$start_crate,$end_crate" >> "$filtering_report"
	fi
done

cp "$filtering_report_final" "$filtering_report"
