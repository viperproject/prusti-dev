#!/bin/bash

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

# Get the root directory of the crate, which is the first argument or the current folder
CRATE_ROOT="$(cd "${1:-.}" && pwd)"
cd "$CRATE_ROOT"

if [[ ! -r "$CRATE_ROOT/Cargo.toml" ]]; then
    error "Path '$CRATE_ROOT' does not look like the source of a crate"
    exit 1
fi


EVALUATION_TIMEOUT="${EVALUATION_TIMEOUT:-900}"
info "Using EVALUATION_TIMEOUT=$EVALUATION_TIMEOUT seconds"

export PRUSTI_CHECK_PANICS="${PRUSTI_CHECK_PANICS:-false}"
info "Using PRUSTI_CHECK_PANICS=$PRUSTI_CHECK_PANICS"

export PRUSTI_CHECK_BINARY_OPERATIONS="${PRUSTI_CHECK_BINARY_OPERATIONS:-false}"
info "Using PRUSTI_CHECK_BINARY_OPERATIONS=$PRUSTI_CHECK_BINARY_OPERATIONS"

export RUSTUP_TOOLCHAIN="$(cat "$DIR/../../rust-toolchain")"
info "Using RUSTUP_TOOLCHAIN=$RUSTUP_TOOLCHAIN"

CARGO_PRUSTI="$DIR/../../bin/cargo-prusti"
info "Using CARGO_PRUSTI=$CARGO_PRUSTI"

CARGO_PRUSTI_FILTER="$DIR/../../bin/cargo-prusti-filter"
info "Using CARGO_PRUSTI_FILTER=$CARGO_PRUSTI_FILTER"

export LOG_LEVEL=info

# Make sure that the "standard" compilation uses the same compiler flags as Prusti uses
export RUSTFLAGS="-Zborrowck=mir -Zpolonius -Znll-facts"
export POLONIUS_ALGORITHM="Naive"

export RUST_BACKTRACE=1
# Sometimes Prusti is run over dependencies, in a different folder. So, make sure that the whitelist is always enabled.
export PRUSTI_ENABLE_WHITELIST=true

info "Start verification"

# Timeout in seconds
timeout -k 10 $EVALUATION_TIMEOUT "$CARGO_PRUSTI" -j 1 || exit_status="$?"
if [[ "$exit_status" != "0" ]]; then
    info "Prusti verification failed with exit status $exit_status."
    if [[ "$exit_status" == "124" ]]; then
        exit 124
    else
        exit 101
    fi
else
    exit 0
fi
