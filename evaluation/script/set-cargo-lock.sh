#!/bin/bash

# Get the directory in which this script is contained
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"

if [[ ! -d "$1" ]]; then
	echo "It looks like CRATE_DOWNLOAD_DIR (the first argument) does not exist: '$1'"
	exit 1
fi

# Get the folder in which to download all the crates
CRATE_DOWNLOAD_DIR="$(cd "${1:-.}" && pwd)"

if [[ ! -d "$CRATE_DOWNLOAD_DIR/000_libc" ]]; then
	error "It looks like CRATE_DOWNLOAD_DIR is wrong: '$CRATE_DOWNLOAD_DIR'"
	exit 1
fi

for crate_folder in "$CRATE_DOWNLOAD_DIR"/*/; do
    crate=$(basename $crate_folder)
    candidate_lock="$DIR/../crates/locks/$crate.Cargo.lock"
    lock_dst="$crate_folder/source/Cargo.lock"
    if [[ -f "$candidate_lock" ]]; then
        echo "$crate: copying Cargo.lock"
        diff "$lock_dst" "$candidate_lock"
        cp "$candidate_lock" "$lock_dst"
    else
        echo "$crate: no Cargo.lock"
    fi
done
