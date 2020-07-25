#!/bin/bash

# Run cargo-prusti on all the crates (COARSE grained verification)
#
# Usage: script <crate/download/dir> <file/with/list/of/crates> [timeout-per-crate-in-seconds]

set -uo pipefail

info() { echo -e "[-] ($(date '+%Y-%m-%d %H:%M:%S')) ${*}"; }
error() { echo -e "[!] ($(date '+%Y-%m-%d %H:%M:%S')) ${*}"; }

cargoclean() {
	# Clean the artifacts of this project ("bin" or "lib"), but not those of the dependencies
	names="$(cargo metadata --format-version 1 | jq -r '.packages[].targets[] | select( .kind | map(. == "bin" or . == "lib") | any ) | select ( .src_path | contains(".cargo/registry") | . != true ) | .name')"
	for name in $names; do
		cargo clean -p "$name" || cargo clean
	done
}

info "=== Coarse-grained verification ==="

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
VERIFICATION_TIMEOUT="${4:-900}"
info "Using VERIFICATION_TIMEOUT=$VERIFICATION_TIMEOUT seconds"

CARGO_PRUSTI="$DIR/../../bin/cargo-prusti"
info "Using CARGO_PRUSTI=$CARGO_PRUSTI"

export PRUSTI_CHECK_PANICS="${PRUSTI_CHECK_PANICS:-false}"
info "Using PRUSTI_CHECK_PANICS=$PRUSTI_CHECK_PANICS"

export PRUSTI_CHECK_BINARY_OPERATIONS="${PRUSTI_CHECK_BINARY_OPERATIONS:-false}"
info "Using PRUSTI_CHECK_BINARY_OPERATIONS=$PRUSTI_CHECK_BINARY_OPERATIONS"

export PRUSTI_ENCODE_UNSIGNED_NUM_CONSTRAINT="${PRUSTI_ENCODE_UNSIGNED_NUM_CONSTRAINT:-false}"
info "Using PRUSTI_ENCODE_UNSIGNED_NUM_CONSTRAINT=$PRUSTI_ENCODE_UNSIGNED_NUM_CONSTRAINT"

start_date="$(date '+%Y-%m-%d-%H%M%S')"
verification_report="$CRATE_DOWNLOAD_DIR/coarse-grained-verification-report-$start_date.csv"
verification_report_final="$CRATE_DOWNLOAD_DIR/coarse-grained-verification-report.csv"
echo "Crate name,Successful verification,Verified items,Successful items,Duration (s),Exit status,Start,End,Parsing duration,Type-checking duration,Encoding duration,Verification duration" > "$verification_report"
info "Report: '$verification_report'"

info "Run verification on $(cat "$CRATES_LIST_PATH" | wc -l) crates"

# Make sure that the "standard" compilation uses the same compiler flags as Prusti uses.
# Also, hide warning messages.
export RUSTFLAGS="-Zborrowck=mir -Zpolonius -Znll-facts -Awarnings" # "-C overflow-check=yes"
export POLONIUS_ALGORITHM="Naive"
export RUST_BACKTRACE=1
export PRUSTI_FULL_COMPILATION=true

export RUSTUP_TOOLCHAIN="$(cat "$DIR/../../rust-toolchain")"
info "Using RUSTUP_TOOLCHAIN=$RUSTUP_TOOLCHAIN"

cat "$CRATES_LIST_PATH" | while read crate_name; do
	info "=== Crate '$crate_name' ==="
	CRATE_DIR="$CRATE_DOWNLOAD_DIR/$crate_name"
	CRATE_ROOT="$CRATE_DIR/source"
	cd "$CRATE_ROOT"

	log_file="$CRATE_DIR/verify-coarse-grained-$start_date.log"

	start_crate="$(date '+%Y-%m-%d %H:%M:%S')"

	# Save disk space
	rm -rf log/ nll-facts/
	# This is important! Without this, NLL facts are not recomputed and dumped to nll-facts.
	rm -rf target/*/incremental/

	# Full cargo clean
	cargo clean

	(
		echo "CHECK_PANICS = $PRUSTI_CHECK_PANICS"
		echo "CHECK_BINARY_OPERATIONS = $PRUSTI_CHECK_BINARY_OPERATIONS"
		echo "ENCODE_UNSIGNED_NUM_CONSTRAINT = $PRUSTI_ENCODE_UNSIGNED_NUM_CONSTRAINT"
		echo "REPORT_SUPPORT_STATUS = false"
		echo "SKIP_UNSUPPORTED_FUNCTIONS = true"
	) > "$CRATE_ROOT/Prusti.toml"

	exit_status="0"
	SECONDS=0
	timeout -k 10 "$VERIFICATION_TIMEOUT" "$CARGO_PRUSTI" 2>&1 | tee "$log_file" || exit_status="$?"
	duration="$SECONDS"

	verified_items="$( (egrep 'Received [0-9]+ items to be verified' "$log_file" | cut -d ' ' -f 6 | sed 's/$/+/' | tr '\n' ' ' ; echo "0") | bc )"
	successful_items="$( (egrep 'Successful verification of [0-9]+ items' "$log_file" | cut -d ' ' -f 4 | sed 's/$/+/' | tr '\n' ' ' ; echo "0") | bc )"

	parsing_duration="$(egrep 'Parsing of annotations successful \(.* seconds\)' "$log_file" | tail -1 | cut -d ' ' -f 9 | sed 's/(//')"
	type_checking_duration="$(egrep 'Type-checking of annotations successful \(.* seconds\)' "$log_file" | tail -1 | cut -d ' ' -f 9 | sed 's/(//')"
	encoding_duration="$(egrep 'Encoding to Viper successful \(.* seconds\)' "$log_file" | tail -1 | cut -d ' ' -f 9 | sed 's/(//' | sed 's/^$/0.0/')"
	verification_duration="$(egrep 'Verification complete \(.* seconds\)' "$log_file" | tail -1 | cut -d ' ' -f 7 | sed 's/(//' | sed 's/^$/0.0/')"

	if [[ "$exit_status" == "0" ]]; then
		end_crate="$(date '+%Y-%m-%d %H:%M:%S')"
		info "Successful verification ($verified_items/$successful_items)"
		echo "$crate_name,true,$verified_items,$successful_items,$duration,$exit_status,$start_crate,$end_crate,$parsing_duration,$type_checking_duration,$encoding_duration,$verification_duration" >> "$verification_report"
	else
		end_crate="$(date '+%Y-%m-%d %H:%M:%S')"
		info "Verification failed with exit status $exit_status ($verified_items/$successful_items)"
		echo "$crate_name,false,$verified_items,$successful_items,$duration,$exit_status,$start_crate,$end_crate,$parsing_duration,$type_checking_duration,$encoding_duration,$verification_duration" >> "$verification_report"
	fi
done

cp "$verification_report" "$verification_report_final"
