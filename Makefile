SHELL := /usr/bin/env bash

ifeq ($(shell uname), Darwin)
	LIB_EXT = dylib
	TOOLCHAIN_SUFFIX = apple-darwin
else
	LIB_EXT = so
	TOOLCHAIN_SUFFIX = unknown-linux-gnu
endif

RUST_LOG ?= prusti=info
# TODO: remove for testing
RUST_TEST_THREADS ?= 1
JAVA_HOME ?= /usr/lib/jvm/default-java
RUN_FILE ?= prusti/tests/verify/pass/no-annotations/assert-true.rs
RUN_FILE_FOLDER=$(shell dirname $(RUN_FILE))
ABS_JAVA_HOME=$(shell perl -MCwd -le 'print Cwd::abs_path shift' "$(JAVA_HOME)")
JAVA_LIBJVM_DIR=$(shell dirname "$(shell find "$(ABS_JAVA_HOME)" -name "libjvm.$(LIB_EXT)")")
RUSTUP_TOOLCHAIN=$(shell cat rust-toolchain)
RUST_VERSION = $(RUSTUP_TOOLCHAIN)-x86_64-$(TOOLCHAIN_SUFFIX)
COMPILER_PATH = $$HOME/.rustup/toolchains/$(RUST_VERSION)
LIB_PATH = $(COMPILER_PATH)/lib:$(JAVA_LIBJVM_DIR):./target/debug:./target/debug/deps
RELEASE_LIB_PATH = $(COMPILER_PATH)/lib:$(JAVA_LIBJVM_DIR):./target/release:./target/release/deps
PRUSTI_DRIVER=./target/debug/prusti-driver
PRUSTI_DRIVER_RELEASE=./target/release/prusti-driver
Z3_EXE ?= $(shell which z3)

SHARED_ENV_VARS = JAVA_HOME=$(JAVA_HOME) RUST_TEST_THREADS=$(RUST_TEST_THREADS) Z3_EXE=$(Z3_EXE)

SET_ENV_VARS = $(SHARED_ENV_VARS) LD_LIBRARY_PATH=$(LIB_PATH) RUST_BACKTRACE=1
SET_RELEASE_ENV_VARS = $(SHARED_ENV_VARS) LD_LIBRARY_PATH=$(RELEASE_LIB_PATH)

default: build

fmt:
	rustup run nightly cargo fmt --all || true

fix:
	$(SET_ENV_VARS) cargo fix $(CARGO_ARGS)

check:
	$(SET_ENV_VARS) cargo check --all $(CARGO_ARGS)

build:
	$(SET_ENV_VARS) cargo build --all $(CARGO_ARGS)

release:
	$(SET_ENV_VARS) cargo build --release --all $(CARGO_ARGS)

release-profile:
	$(SET_ENV_VARS) \
	CARGO_INCREMENTAL=0 \
	RUSTFLAGS="-Zprofile -Ccodegen-units=1 -Copt-level=0 -Cinline-threshold=0 -Clink-dead-code" \
	cargo build --release --all

test: build clean-nested
	$(SET_ENV_VARS) \
	cargo test --all

test-examples: build clean-nested
	$(SET_ENV_VARS) \
	cargo test -p prusti

test-viper-crate: build clean-nested
	$(SET_ENV_VARS) \
	cargo test -p viper

test-server-crate: build clean-nested
	$(SET_ENV_VARS) \
	cargo test -p prusti-server

test-deep: clean-nested
	$(SET_ENV_VARS) \
	PRUSTI_CHECK_FOLDUNFOLD_STATE=1 \
	cargo test --all

bench:
	$(SET_ENV_VARS) cargo bench --all

run: build
	$(SET_ENV_VARS) RUST_LOG=$(RUST_LOG) \
	$(PRUSTI_DRIVER) \
		-L $(COMPILER_PATH)/lib/rustlib/x86_64-unknown-linux-gnu/lib/ \
		--extern prusti_contracts=$(wildcard ./target/debug/deps/libprusti_contracts-*.rlib) \
		$(RUN_FILE)

run-release: release
	$(SET_RELEASE_ENV_VARS) RUST_LOG=$(RUST_LOG) \
	$(PRUSTI_DRIVER_RELEASE) \
		-L $(COMPILER_PATH)/lib/rustlib/x86_64-unknown-linux-gnu/lib/ \
		--extern prusti_contracts=$(wildcard ./target/release/deps/libprusti_contracts-*.rlib) \
		$(RUN_FILE)

run-release-profile: release
	$(SET_RELEASE_ENV_VARS) RUST_LOG=$(RUST_LOG) \
    valgrind --tool=callgrind \
	$(PRUSTI_DRIVER_RELEASE) \
		-L $(COMPILER_PATH)/lib/rustlib/x86_64-unknown-linux-gnu/lib/ \
		--extern prusti_contracts=$(wildcard ./target/release/deps/libprusti_contracts-*.rlib) \
		$(RUN_FILE)
	@echo "Now run 'kcachegrind callgrind.out.*'"

run-release-flamegraph: release
	$(SET_RELEASE_ENV_VARS) RUST_LOG=$(RUST_LOG) \
    perf record -F 99 --call-graph=dwarf,32000 \
	$(PRUSTI_DRIVER_RELEASE) \
		-L $(COMPILER_PATH)/lib/rustlib/x86_64-unknown-linux-gnu/lib/ \
		--extern prusti_contracts=$(wildcard ./target/release/deps/libprusti_contracts-*.rlib) \
		$(RUN_FILE)
	@echo "Now run 'flamegraph-rust-perf > flame.svg'"

run-release-prusti-rustc-flamegraph: release
	perf record -F 99 --call-graph=dwarf,32000 \
	    ./target/release/prusti-rustc $(RUN_FILE)
	@echo "Now run 'flamegraph-rust-perf > flame.svg'"

run-release-prusti-rustc-timechart: release
	perf timechart record \
	    ./target/release/prusti-rustc $(RUN_FILE)
	@echo "Now run 'perf timechart'"

run-release-prusti-rustc-timechart-io: release
	perf timechart record -I \
	    ./target/release/prusti-rustc $(RUN_FILE)
	@echo "Now run 'perf timechart'"

update:
	cargo update

docs: update
	$(SET_ENV_VARS) cargo doc --all

clippy: clean
	$(SET_ENV_VARS) cargo clippy --all

publish-docker-images:
	docker push fpoli/prusti-base
	docker push fpoli/prusti-artefact

build-docker-images:
	docker build -t fpoli/prusti-base --build-arg RUST_TOOLCHAIN="$(RUSTUP_TOOLCHAIN)" -f docker/base.Dockerfile docker/
	docker build -t rust-nightly -f docker/playground.Dockerfile .
	docker build -t fpoli/prusti-artefact -f docker/artefact.Dockerfile .

clean: clean-nested
	cargo clean
	find . -name '*.bk' -delete
	rm -rf log
	rm -rf nll-facts
	rm -rf prusti/log
	rm -rf prusti/nll-facts

.PHONY: clean-nested
clean-nested:
	rm -rf prusti/tests/**/log/
	rm -rf prusti/tests/**/nll-facts/

todo:
	git grep -i "todo\|fixme\|xxx\|hack"

demo:
	vagrant up
