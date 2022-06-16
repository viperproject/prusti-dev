#!/usr/bin/env bash

set -euo pipefail

if [ $# -ne 2 ]; then
    echo "Usage: ./compare-performance.sh OLD_BRANCH NEW_BRANCH"
fi

OLD_BRANCH="$1"
NEW_BRANCH="$2"
ORIG_BRANCH=$(git branch --show-current)

git checkout "$OLD_BRANCH"

./x.py build --release
./x.py run-benchmarks "$OLD_BRANCH"

git checkout "$NEW_BRANCH"

./x.py build --release
./x.py run-benchmarks "$NEW_BRANCH"

git checkout "$ORIG_BRANCH"
