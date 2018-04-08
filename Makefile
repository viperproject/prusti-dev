SHELL := /bin/bash
JAVA_HOME=/usr/lib/jvm/default-java
LD_LIBRARY_PATH=${JAVA_HOME}/jre/lib/amd64/server

build:
	cargo build

test:
	cargo test --verbose -- --nocapture
