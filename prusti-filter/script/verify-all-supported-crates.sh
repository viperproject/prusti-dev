#!/bin/bash

set -euo pipefail

# Get the directory in which this script is contained
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"
SCRIPT_NAME="$(basename -s '.sh' "$0")"

# Get the folder in which all the crates has been downloaded
CRATE_DOWNLOAD_DIR="$(cd "${1:-.}" && pwd)"
cd "$CRATE_DOWNLOAD_DIR"

rustup override set nightly-2018-06-27

if [[ ! -d "$CRATE_DOWNLOAD_DIR/000_libc" ]]; then
	echo "It looks like CRATE_DOWNLOAD_DIR is wrong: '$CRATE_DOWNLOAD_DIR'"
	exit 1
fi

for crate in "$CRATE_DOWNLOAD_DIR"/*/; do
	log_file="${crate}${SCRIPT_NAME}.log"
	crate_source_dir="${crate}source"
	crate_name="$(basename "$crate")"
	(
		echo ""
		echo "===== Verify crate '$crate_name' ($(date '+%Y-%m-%d %H:%M:%S')) ====="
		echo ""
		SECONDS=0
		# Timeout of 1 hour
		timeout 3600 "$DIR/verify-supported.sh" "$crate_source_dir" 2>&1
		exit_status="$?"
		duration="$SECONDS"
		whitelist_items="$(grep '"' "$crate_source_dir/Prusti.toml" | wc -l)"
		echo "Exit status: $exit_status"
		echo "Duration: $duration seconds"
		echo "Items in whitelist: $whitelist_items"
		echo ""
		echo "Summary for crate '$crate_name': exit status $exit_status, $whitelist_items items, $duration seconds ($(date '+%Y-%m-%d %H:%M:%S'))"
	) | tee "$log_file" || true
done
