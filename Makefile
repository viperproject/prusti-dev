SHELL := /bin/bash
IMAGE_VERSION=2017-12-10
IMAGE_NAME="vakaras/prusti:${IMAGE_VERSION}"
export RUSTC=
LOG_LEVEL=error

run:
	RUST_LOG=prusti=${LOG_LEVEL} ${RUSTC} \
		-L target/debug/ \
		-Z mir-emit-validate=1 \
		-Z extra-plugins=prusti \
		-Z borrowck=mir \
		-Z nll \
		tests/lint.rs

build:
	cargo build

test:
	cargo test

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
