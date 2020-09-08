#!/bin/bash

if [[ ! -d "$1" ]]; then
	echo "It looks like CRATE_DOWNLOAD_DIR (the first argument) does not exist: '$1'"
	exit 1
fi

# Get the folder in which to download all the crates
CRATE_DOWNLOAD_DIR="$(cd "${1:-.}" && pwd)"

if [[ ! -z "$(ls -A "$CRATE_DOWNLOAD_DIR")" ]]; then
	echo "It looks like CRATE_DOWNLOAD_DIR (the first argument) is not empty: '$CRATE_DOWNLOAD_DIR'"
	exit 1
fi

#   0 id=libc name=libc
mkdir -p "$CRATE_DOWNLOAD_DIR/000_libc"
wget -c "https://crates.io/api/v1/crates/libc/0.2.43/download" -O "$CRATE_DOWNLOAD_DIR/000_libc/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/000_libc/source"
tar -xf "$CRATE_DOWNLOAD_DIR/000_libc/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/000_libc/source" --strip-components=1

#   1 id=bitflags name=bitflags
mkdir -p "$CRATE_DOWNLOAD_DIR/001_bitflags"
wget -c "https://crates.io/api/v1/crates/bitflags/1.0.4/download" -O "$CRATE_DOWNLOAD_DIR/001_bitflags/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/001_bitflags/source"
tar -xf "$CRATE_DOWNLOAD_DIR/001_bitflags/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/001_bitflags/source" --strip-components=1

#   2 id=log name=log
mkdir -p "$CRATE_DOWNLOAD_DIR/002_log"
wget -c "https://crates.io/api/v1/crates/log/0.4.5/download" -O "$CRATE_DOWNLOAD_DIR/002_log/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/002_log/source"
tar -xf "$CRATE_DOWNLOAD_DIR/002_log/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/002_log/source" --strip-components=1
