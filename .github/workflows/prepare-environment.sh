#!/usr/bin/env bash

sudo apt-get install -y build-essential pkg-config gcc libssl-dev openjdk-8-jdk

echo "::set-env name=LD_LIBRARY_PATH::"$(dirname "$(find "$JAVA_HOME" -name "libjvm.so")")""

wget -q "http://viper.ethz.ch/downloads/ViperToolsNightlyLinux.zip"
unzip ViperToolsNightlyLinux.zip -d viper_tools
rm ViperToolsNightlyLinux.zip
echo "::set-env name=VIPER_HOME::$(pwd)/viper_tools/backends/"
echo "::set-env name=Z3_EXE::$(pwd)/viper_tools/z3/bin/z3"
