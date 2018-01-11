SHELL := /bin/bash
IMAGE_VERSION=2017-12-10
IMAGE_NAME="vakaras/prusti:${IMAGE_VERSION}"
LOG_LEVEL=error

run:
	RUST_LOG=prusti=${LOG_LEVEL} \
	LD_LIBRARY_PATH=~/.rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/ \
	target/debug/prusti-driver \
		-L target/debug/ \
		--extern prusti_contracts=$(wildcard target/debug/deps/libprusti_contracts-*.rlib) \
		-Z mir-emit-validate=1 \
		-Z borrowck=mir \
		-Z nll \
		tests/typecheck/fail/specification_type_error.rs

build:
	cargo build

test:
	cargo test

clean:
	cargo clean
	rm -f lint

doc:
	cargo rustdoc -- \
		--no-defaults \
		--passes collapse-docs \
		--passes unindent-comments \
		--passes strip-priv-imports

build_release:
	cargo build --release

build_image:
	sudo docker build -t ${IMAGE_NAME} docker

build_image_as_rust_nightly: build_image
	sudo docker build -t rust-nightly docker
