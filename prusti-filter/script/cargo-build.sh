#!/bin/bash
# File: extractor/script/cargo-build.sh

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"

COMPILER_PATH="$(cd $DIR/.. && rustup which rustc | sed 's/\/bin\/rustc$//')"

export LD_LIBRARY_PATH=${COMPILER_PATH}/lib:${DIR}/../../target/debug/deps

export RUSTC=${DIR}/../script/rustc.sh

cargo build
