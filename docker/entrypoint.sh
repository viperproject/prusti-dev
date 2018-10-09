#!/bin/bash

set -eu

#timeout=${PLAYGROUND_TIMEOUT:-60}
timeout=60

timeout --signal=KILL ${timeout} "$@"
