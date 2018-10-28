#!/bin/bash

set -euo pipefail

info() { echo -e "[-] ${*}"; }
error() { echo -e "[!] ${*}"; }

# Get the directory in which this script is contained
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"

# Get the root directory of the crate, which is the first argument or the current folder
CRATE_ROOT="$(cd "${1:-.}" && pwd)"
cd "$CRATE_ROOT"

if [[ ! -r "$CRATE_ROOT/Cargo.toml" ]]; then
	error "Path '$CRATE_ROOT' does not look like the source of a crate"
	exit 1
fi

cargoclean() {
	# Clean the artifacts of this project ("bin" or "lib"), but not those of the dependencies
	names="$(cargo metadata --format-version 1 | jq -r '.packages[].targets[] | select( .kind | map(. == "bin" or . == "lib") | any ) | select ( .src_path | contains(".cargo/registry") | . != true ) | .name')"
	for name in $names; do
		cargo clean -p "$name" || cargo clean
	done
}

export RUSTCFLAGS="-Zborrowck=mir -Zpolonius"

info "Run standard compilation"
exit_status="0"
# Timeout of 30 minutes
timeout 1800 cargo build || exit_status="$?" && true
if [[ "$exit_status" != "0" ]]; then
	info "The crate does not compile. Skip verification."
	exit 42
fi

if [[ ! -r "$CRATE_ROOT/results.json" ]]; then
	info "Filter supported procedures"
	export RUSTC="$DIR/rustc.sh"
	export RUST_BACKTRACE=1
	cargoclean
	cargo build
	unset RUSTC
	unset RUST_BACKTRACE
fi

supported_procedures="$(jq '.functions[] | select(.procedure.restrictions | length == 0) | .node_path' "$CRATE_ROOT/results.json")"

info "Prepare whitelist ($(echo "$supported_procedures" | grep . | wc -l) items)"

(
	echo "CHECK_PANICS = false"
	echo "ENABLE_WHITELIST = true"
	echo "WHITELIST = ["
	echo "$supported_procedures" | sed 's/$/,/' | sed '$ s/.$//'
	echo "]"
) > "$CRATE_ROOT/Prusti.toml"

info "Start verification"

# Save disk space
rm -rf log/ nll-facts/
# This is important! Without this, NLL facts are not recomputed and dumped to nll-facts.
rm -rf target/*/incremental/
# Optional: generate the final binaries
#export PRUSTI_FULL_COMPILATION=true
export RUSTC="$DIR/../../docker/prusti"
export RUST_BACKTRACE=1
cargoclean
# Timeout of 30 minutes
timeout 1800 cargo build -j 1
