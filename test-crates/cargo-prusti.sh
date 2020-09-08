#!/bin/bash

# © 2020, ETH Zurich
#
# Licensed under the Mozilla Public License Version 2.0 (see LICENSE or
# http://www.mozilla.org/MPL/2.0/). This file may not be copied,
# modified, or distributed except according to those terms.

info() { test -n "$PRUSTI_DEBUG" && >&2 echo -e "[-] ${*}"; }
error() { >&2 echo -e "[!] ${*}"; }

# Get the directory in which this script is contained
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"
info "Executing Prusti script located in '$DIR'"

PRUSTI_ROOT="$DIR/.."

# Set PRUSTI_RUSTC
if [ -x "$PRUSTI_ROOT/target/debug/cargo-prusti" ]; then
	[[ "$PRUSTI_ROOT/target/debug/cargo-prusti" -nt "$PRUSTI_RUSTC" ]] \
	    && CARGO_PRUSTI="$PRUSTI_ROOT/target/debug/cargo-prusti"
fi
if [ -x "$PRUSTI_ROOT/target/release/cargo-prusti" ]; then
	[[ "$PRUSTI_ROOT/target/release/cargo-prusti" -nt "$CARGO_PRUSTI" ]] \
	    && CARGO_PRUSTI="$PRUSTI_ROOT/target/release/cargo-prusti"
fi
if [ -z "$CARGO_PRUSTI" ]; then
	error "Unable to find CARGO_PRUSTI."
	error "It looks like Prusti has not been compiled or installed properly."
	exit 1
else
    info "Using CARGO_PRUSTI '$CARGO_PRUSTI'"
fi

info "Arguments: $*"
info "Run Cargo-Prusti...\n"
exec "${CARGO_PRUSTI}" "$@"
