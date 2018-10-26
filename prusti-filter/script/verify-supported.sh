#!/bin/bash

set -euo pipefail

info() { echo -e "[-] ${*}"; }
error() { echo -e "[!] ${*}"; }

# Get the directory in which this script is contained
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"

# Get the root directory of the crate, which is the first argument or the current folder
CRATE_ROOT="$(cd "${1:-.}" && pwd)"
cd "$CRATE_ROOT"

rustup override set nightly-2018-06-27

if [[ ! -r "$CRATE_ROOT/Cargo.toml" ]]; then
	error "Path '$CRATE_ROOT' does not look like the source of a crate"
	exit 1
fi

info "Filter supported procedures"

export RUSTC="$DIR/rustc.sh"
cargo clean
cargo build

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

export PRUSTI_FULL_COMPILATION=true
export RUSTC="$DIR/../../docker/prusti"
cargo clean
cargo build --verbose
