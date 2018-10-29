SHELL := /bin/bash
RUN_FILE = tests/typecheck/pass/lint.rs
RUN_FILE_FOLDER = $(shell dirname ${RUN_FILE})
RUST_LOG ?= prusti=info
RUST_TEST_THREADS ?= 1
JAVA_HOME ?= /usr/lib/jvm/default-java
RUN_FILE ?= prusti/tests/typecheck/pass/lint.rs
RUN_FILE_FOLDER=$(shell dirname ${RUN_FILE})
JAVA_LIBJVM_DIR=$(shell dirname "$(shell find "$(shell readlink -f ${JAVA_HOME})" -name "libjvm.so")")
RUST_VERSION = nightly-2018-06-27-x86_64-unknown-linux-gnu
COMPILER_PATH = $$HOME/.rustup/toolchains/${RUST_VERSION}
LIB_PATH = ${COMPILER_PATH}/lib:${JAVA_LIBJVM_DIR}:./target/debug:./target/debug/deps
PRUSTI_DRIVER=./target/debug/prusti-driver

SET_ENV_VARS = LD_LIBRARY_PATH=$(LIB_PATH) JAVA_HOME=$(JAVA_HOME) RUST_TEST_THREADS=$(RUST_TEST_THREADS)

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
	$(SET_ENV_VARS) \
	PRUSTI_CHECK_UNREACHABLE_TERMINATORS=1 \
	PRUSTI_CHECK_FOLDUNFOLD_STATE=1 \
	cargo test --all

quick-test:
	$(SET_ENV_VARS) \
	cargo test --all

bench:
	$(SET_ENV_VARS) cargo bench --all

run:
	@echo "The best way to run Prusti is with `./docker/prusti`"
	$(SET_ENV_VARS) RUST_LOG=$(RUST_LOG) \
	$(PRUSTI_DRIVER) \
		-L ${COMPILER_PATH}/lib/rustlib/x86_64-unknown-linux-gnu/lib/ \
		--extern prusti_contracts=$(wildcard ./target/debug/deps/libprusti_contracts-*.rlib) \
		$(RUN_FILE)

update:
	cargo update

docs: update
	$(SET_ENV_VARS) cargo doc --all

clippy: clean
	$(SET_ENV_VARS) cargo clippy --all

clean:
	cargo clean
	find . -name '*.bk' -delete
	rm -rf log
	rm -rf nll-facts
	rm -rf prusti/log
	rm -rf prusti/nll-facts

todo:
	git grep -i "todo\|fixme\|xxx\|hack"
