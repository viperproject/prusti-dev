#!/bin/bash

# Run cargo-prusti on all the crates (FINE grained verification)
#
# Usage: script <crate/download/dir> <file/with/list/of/crates> <file_name/of/whitelist> [timeout-per-crate-in-seconds]

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

# Get the filename of the whitelist
WHITELIST_FILENAME="$3"

# Compilation timeout
VERIFICATION_TIMEOUT="${4:-900}"
info "Using VERIFICATION_TIMEOUT=$VERIFICATION_TIMEOUT seconds"

CARGO_PRUSTI="$DIR/../../docker/cargo-prusti"
info "Using CARGO_PRUSTI_FILTER=$CARGO_PRUSTI"

export PRUSTI_CHECK_PANICS="${PRUSTI_CHECK_PANICS:-false}"
info "Using PRUSTI_CHECK_PANICS=$PRUSTI_CHECK_PANICS"

export PRUSTI_CHECK_BINARY_OPERATIONS="${PRUSTI_CHECK_BINARY_OPERATIONS:-false}"
info "Using PRUSTI_CHECK_BINARY_OPERATIONS=$PRUSTI_CHECK_BINARY_OPERATIONS"

verification_report="$CRATE_DOWNLOAD_DIR/coarse-grained-verification-report-$WHITELIST_FILENAME-$(date '+%Y-%m-%d-%H%M%S').csv"
echo "'Crate name', 'Procedure', 'Verifies fine', 'Duration (s)', 'Exit status'" > "$verification_report"
info "Report: '$verification_report'"

info "Run verification on $(cat "$CRATES_LIST_PATH" | wc -l) crates"

# Make sure that the "standard" compilation uses the same compiler flags as Prusti uses
export RUSTFLAGS="-Zborrowck=mir -Zpolonius -Znll-facts"
export POLONIUS_ALGORITHM="Naive"
export RUST_BACKTRACE=1
export PRUSTI_FULL_COMPILATION=true
export PRUSTI_ENABLE_WHITELIST=true

export RUSTUP_TOOLCHAIN="$(cat $DIR/../../rust-toolchain)"
info "Using RUSTUP_TOOLCHAIN=$RUSTUP_TOOLCHAIN"

cat "$CRATES_LIST_PATH" | while read crate_name; do
	info "=== Crate '$crate_name' ==="
	CRATE_DIR="$CRATE_DOWNLOAD_DIR/$crate_name"
	CRATE_ROOT="$CRATE_DIR/source"
	cd "$CRATE_ROOT"

	WHITELIST_FILE="$CRATE_DIR/$WHITELIST_FILENAME"

	# Save disk space
	rm -rf log/ nll-facts/
	# This is important! Without this, NLL facts are not recomputed and dumped to nll-facts.
	rm -rf target/*/incremental/

	cat "$WHITELIST_FILE" | while read procedure_path; do
		info "=== Crate '$crate_name' procedure $procedure_path ==="

		(
			echo "CHECK_PANICS = $PRUSTI_CHECK_PANICS"
			echo "CHECK_BINARY_OPERATIONS = $PRUSTI_CHECK_BINARY_OPERATIONS"
			echo "ENABLE_WHITELIST = true"
			echo "WHITELIST = ["
			echo "  $procedure_path"
			echo "]"
		) > "$CRATE_ROOT/Prusti.toml"

		cargoclean

		exit_status="0"
		SECONDS=0
		timeout -k 10 "$VERIFICATION_TIMEOUT" "$CARGO_PRUSTI" -j 1 || exit_status="$?"
		duration="$SECONDS"
		if [[ "$exit_status" == "0" ]]; then
			info "Successful verification"
			echo "'$crate_name', $procedure_path, true, $duration, $exit_status" >> "$verification_report"
		else
			info "Verification failed with exit status $exit_status."
			echo "'$crate_name', $procedure_path, false, $duration, $exit_status" >> "$verification_report"
		fi
	done
done
