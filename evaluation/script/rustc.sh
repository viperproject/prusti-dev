#!/bin/bash
# File: extractor/script/rustc.sh

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"

command="${DIR}/../../target/debug/prusti-filter $@"

#echo $command >> /tmp/out

exec $command
