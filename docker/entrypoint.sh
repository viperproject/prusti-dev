#!/bin/bash

set -eu

#timeout=${PLAYGROUND_TIMEOUT:-60}
timeout=300

timeout --signal=KILL ${timeout} "$@"
