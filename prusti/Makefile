SHELL := /bin/bash
IMAGE_VERSION=2017-12-10
IMAGE_NAME="vakaras/prusti:${IMAGE_VERSION}"
LOG_LEVEL=error
RUST_TEST_THREADS ?= 1
RUN_FILE ?= tests/typecheck/pass/lint.rs
RUN_FILE_FOLDER=$(shell dirname ${RUN_FILE})
STDERR_FILE=$(RUN_FILE:.rs=.stderr)
JAVA_HOME ?= $(shell readlink -f /usr/lib/jvm/default-java)
JAVA_LIBJVM_DIR=$(shell dirname "$(shell find "$(shell readlink -f ${JAVA_HOME})" -name "libjvm.so")")
RUSTUP_TOOLCHAIN = $(shell cat ../rust-toolchain)
RUST_VERSION=${RUSTUP_TOOLCHAIN}-x86_64-unknown-linux-gnu
COMPILER_PATH=$$HOME/.rustup/toolchains/${RUST_VERSION}
LIB_PATH=${COMPILER_PATH}/lib:${JAVA_LIBJVM_DIR}:../target/debug:../target/debug/deps
RELEASE_LIB_PATH = ${COMPILER_PATH}/lib:${JAVA_LIBJVM_DIR}:../target/release:../target/release/deps
PRUSTI_DRIVER=../target/debug/prusti-driver
PRUSTI_DRIVER_RELEASE=../target/release/prusti-driver

SET_ENV_VARS = LD_LIBRARY_PATH=$(LIB_PATH) JAVA_HOME=$(JAVA_HOME) RUST_TEST_THREADS=$(RUST_TEST_THREADS)
SET_RELEASE_ENV_VARS = LD_LIBRARY_PATH=$(RELEASE_LIB_PATH) JAVA_HOME=$(JAVA_HOME) RUST_TEST_THREADS=$(RUST_TEST_THREADS)

run:
	@echo "The best way to run Prusti is with `./docker/prusti`"
	$(SET_ENV_VARS) \
	RUST_LOG=${LOG_LEVEL} \
	${PRUSTI_DRIVER} \
		-L ${COMPILER_PATH}/lib/rustlib/x86_64-unknown-linux-gnu/lib/ \
		--extern prusti_contracts=$(wildcard ../target/debug/deps/libprusti_contracts-*.rlib) \
		${RUN_FILE}

run_release:
	@echo "The best way to run Prusti is with `./docker/prusti`"
	$(SET_RELEASE_ENV_VARS) \
	RUST_LOG=${LOG_LEVEL} \
	${PRUSTI_DRIVER_RELEASE} \
		-L ${COMPILER_PATH}/lib/rustlib/x86_64-unknown-linux-gnu/lib/ \
		--extern prusti_contracts=$(wildcard ../target/release/deps/libprusti_contracts-*.rlib) \
		${RUN_FILE}

run-profile:
	@echo "The best way to run Prusti is with `./docker/prusti`"
	$(SET_ENV_VARS) \
	RUST_LOG=${LOG_LEVEL} \
	valgrind --tool=callgrind \
	${PRUSTI_DRIVER} \
		-L ${COMPILER_PATH}/lib/rustlib/x86_64-unknown-linux-gnu/lib/ \
		--extern prusti_contracts=$(wildcard ../target/debug/deps/libprusti_contracts-*.rlib) \
		${RUN_FILE}
	@echo "Now run 'kcachegrind callgrind.out.*'"

run-flamegraph:
	@echo "The best way to run Prusti is with `./docker/prusti`"
	$(SET_ENV_VARS) \
	RUST_LOG=${LOG_LEVEL} \
	perf record -g -F 99 \
	${PRUSTI_DRIVER} \
		-L ${COMPILER_PATH}/lib/rustlib/x86_64-unknown-linux-gnu/lib/ \
		--extern prusti_contracts=$(wildcard ../target/debug/deps/libprusti_contracts-*.rlib) \
		${RUN_FILE}
	@echo "Now run 'flamegraph-rust-perf > flame.svg'"

generate_ui_stderr:
	@echo "The best way to run Prusti is with `./docker/prusti`"
	-$(SET_ENV_VARS) \
	${PRUSTI_DRIVER} \
		--sysroot ${COMPILER_PATH}/lib/ \
		-L ../target/debug/ \
		-L ${COMPILER_PATH}/lib/ \
		-L ${COMPILER_PATH}/lib/rustlib/x86_64-unknown-linux-gnu/lib/ \
		--extern prusti_contracts=$(wildcard ../target/debug/deps/libprusti_contracts-*.rlib) \
		-Z mir-emit-validate=1 \
		-Z borrowck=mir \
		-Awarnings \
		${RUN_FILE} 2> ${STDERR_FILE}
	sed -e "s|${RUN_FILE_FOLDER}|\$$DIR|g" -i ${STDERR_FILE}

build:
	$(SET_ENV_VARS) \
	cargo build --all

test-deep:
	$(SET_ENV_VARS) \
	PRUSTI_CHECK_FOLDUNFOLD_STATE=1 \
	cargo test

test: build
	$(SET_ENV_VARS) \
	cargo test

clean:
	cargo clean
	rm -f lint
	rm -rf log
	mkdir -p log/viper_tmp

doc:
	cargo rustdoc --lib -- \
		-Z unstable-options --document-private-items --enable-commonmark

# cargo install --force clippy
clippy:
	cargo clippy

# cargo install rustfmt-nightly
format_code:
	cargo fmt

build_release:
	$(SET_ENV_VARS) \
	cargo build --release

build_image:
	sudo docker build -t ${IMAGE_NAME} docker

build_image_as_rust_nightly: build_image
	sudo docker build -t rust-nightly docker
