SHELL := /bin/bash
RUST_LOG ?= prusti=info
RUST_TEST_THREADS ?= 1
JAVA_HOME ?= /usr/lib/jvm/default-java
RUN_FILE ?= prusti/tests/typecheck/pass/lint.rs
RUN_FILE_FOLDER=$(shell dirname ${RUN_FILE})
JAVA_LIBJVM_DIR=$(shell dirname "$(shell find "$(shell readlink -f ${JAVA_HOME})" -name "libjvm.so")")
RUSTUP_TOOLCHAIN=$(shell cat rust-toolchain)
RUST_VERSION = ${RUSTUP_TOOLCHAIN}-x86_64-unknown-linux-gnu
COMPILER_PATH = $$HOME/.rustup/toolchains/${RUST_VERSION}
LIB_PATH = ${COMPILER_PATH}/lib:${JAVA_LIBJVM_DIR}:./target/debug:./target/debug/deps
PRUSTI_DRIVER=./target/debug/prusti-driver
PRUSTI_DRIVER_RELEASE=./target/release/prusti-driver

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

run-release:
	@echo "The best way to run Prusti is with `./docker/prusti`"
	$(SET_ENV_VARS) RUST_LOG=$(RUST_LOG) \
	$(PRUSTI_DRIVER_RELEASE) \
		-L ${COMPILER_PATH}/lib/rustlib/x86_64-unknown-linux-gnu/lib/ \
		--extern prusti_contracts=$(wildcard ./target/release/deps/libprusti_contracts-*.rlib) \
		$(RUN_FILE)

run-release-profile:
	@echo "The best way to run Prusti is with `./docker/prusti`"
	$(SET_ENV_VARS) RUST_LOG=$(RUST_LOG) \
    valgrind --tool=callgrind --vex-iropt-register-updates=allregs-at-mem-access \
	${PRUSTI_DRIVER_RELEASE} \
		-L ${COMPILER_PATH}/lib/rustlib/x86_64-unknown-linux-gnu/lib/ \
		--extern prusti_contracts=$(wildcard ./target/release/deps/libprusti_contracts-*.rlib) \
		${RUN_FILE}
	@echo "Now run 'kcachegrind callgrind.out.*'"

run-release-flamegraph:
	@echo "The best way to run Prusti is with `./docker/prusti`"
	$(SET_ENV_VARS) RUST_LOG=$(RUST_LOG) \
    perf record -g -F 99 \
	${PRUSTI_DRIVER_RELEASE} \
		-L ${COMPILER_PATH}/lib/rustlib/x86_64-unknown-linux-gnu/lib/ \
		--extern prusti_contracts=$(wildcard ./target/release/deps/libprusti_contracts-*.rlib) \
		${RUN_FILE}
	@echo "Now run 'flamegraph-rust-perf > flame.svg'"

update:
	cargo update

docs: update
	$(SET_ENV_VARS) cargo doc --all

clippy: clean
	$(SET_ENV_VARS) cargo clippy --all

publish-docker-deps:
	docker build -t fpoli/prusti-deps --build-arg RUST_TOOLCHAIN="${RUSTUP_TOOLCHAIN}" -f docker/Dockerfile-deps docker/
	docker push fpoli/prusti-deps

build-docker-prusti: clean
	docker build --no-cache -t rust-nightly -f docker/Dockerfile-prusti .

clean:
	cargo clean
	find . -name '*.bk' -delete
	rm -rf log
	rm -rf nll-facts
	rm -rf prusti/log
	rm -rf prusti/nll-facts

todo:
	git grep -i "todo\|fixme\|xxx\|hack"
