#!/bin/bash

# To verify a Silver file 'test.sil', run './silicon.sh test.sil'.

set -e

BASEDIR="$(realpath "$(dirname "$0")")"

exec java -Xss30M -Dlogback.configurationFile="$BASEDIR/src/main/resources/logback.xml" -cp $BASEDIR/viper_tools/backends/viperserver.jar viper.silicon.SiliconRunner "$@" --z3Exe=$BASEDIR/viper_tools/z3/bin/z3