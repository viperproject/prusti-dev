#!/bin/bash
#
# Automatically enable passing tests from "prusti-tests/tests_old/".
# Place this script in a subfolder of `prusti-dev`.

set -euf -o pipefail

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

function log() {
    echo "[$(date +%R)] ===== $1 ====="
}

cd "$DIR/.."

if [ ! -f "rust-toolchain" ]; then
    echo "The script is not placed in a subfolder of `prusti-dev`".
    exit 1
fi

log "Build..."
./x.py build

log "Test..."
./x.py test non-existing-asdfasdfasdfasfd

log "Ready. Begin."
files="$(find prusti-tests/tests_old/ -type f -name '*.rs')"
num_files="$(echo "$files" | wc -l)"

log "There are $num_files files"

echo "$files" | while read f
do
    log "Attempt to move '$f'..."
    sleep 0.1
    dst="$(echo "$f" | sed 's/_old//')"
    mkdir -p "$(dirname "$dst")"
    mv "$f" "$dst"
    status="0"
    ./x.py test "$(basename "$dst")" || status="$?"
    if [ "$status" == "0" ]
    then
        log "OK --> Moved '$f' to '$dst'"
    else
        log "ERROR --> Move '$dst' back to '$f'"
        mv "$dst" "$f"
    fi
done

log "End."
