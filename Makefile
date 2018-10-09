SHELL := /bin/bash
RUN_FILE = tests/typecheck/pass/lint.rs
RUN_FILE_FOLDER = $(shell dirname ${RUN_FILE})
RUST_LOG ?= viper=info,prusti_viper=info
RUST_BACKTRACE ?= 1
RUST_TEST_THREADS ?= 1
JAVA_HOME ?= /usr/lib/jvm/default-java
RUST_VERSION = nightly-2018-06-27-x86_64-unknown-linux-gnu
COMPILER_PATH = $$HOME/.rustup/toolchains/${RUST_VERSION}
LIB_PATH = ${COMPILER_PATH}/lib:${JAVA_HOME}/jre/lib/amd64/server:${JAVA_HOME}/lib/server:./target/debug
DRIVER_PATH=./target/debug/prusti-driver

SET_ENV_VARS = RUST_LOG=$(RUST_LOG) RUST_BACKTRACE=$(RUST_BACKTRACE) LD_LIBRARY_PATH=$(LIB_PATH) JAVA_HOME=$(JAVA_HOME) RUST_TEST_THREADS=$(RUST_TEST_THREADS)

default: build

fmt:
	cargo fmt --all || true

check:
	$(SET_ENV_VARS) cargo check --all

build:
	$(SET_ENV_VARS) cargo build --all

release:
	$(SET_ENV_VARS) cargo build --release --all

test:
	$(SET_ENV_VARS) cargo test --all

bench:
	$(SET_ENV_VARS) cargo bench --all

update:
	cargo update

docs: update
	$(SET_ENV_VARS) cargo doc --all

clippy: clean
	$(SET_ENV_VARS) cargo clippy --all

clean:
	cargo clean
	find . -name '*.bk' -delete

todo:
	git grep -i "todo\|fixme\|xxx\|hack"
