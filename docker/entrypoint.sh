#!/bin/bash

# © 2019, ETH Zurich
#
# Licensed under the Mozilla Public License Version 2.0 (see LICENSE or
# http://www.mozilla.org/MPL/2.0/). This file may not be copied,
# modified, or distributed except according to those terms.

set -eu

#timeout=${PLAYGROUND_TIMEOUT:-60}
timeout=300

timeout --signal=KILL ${timeout} "$@"
