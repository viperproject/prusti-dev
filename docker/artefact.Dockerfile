FROM fpoli/prusti-base:latest
MAINTAINER Vytautas Astrauskas "vastrauskas@gmail.com"

# Install Prusti.
ADD . /tmp/prusti-dev
RUN cd /tmp/prusti-dev && \
    cargo build --release && \
	mkdir -p /usr/local/prusti/lib && \
	cp rust-toolchain /usr/local/prusti/rust-toolchain && \
	cp target/release/cargo-prusti /usr/local/prusti/cargo-prusti && \
	cp target/release/prusti-rustc /usr/local/prusti/prusti-rustc && \
	cp target/release/prusti-driver /usr/local/prusti/prusti-driver && \
	cp target/release/libprusti_contracts.rlib /usr/local/prusti/libprusti_contracts.rlib

ENV PATH "/usr/local/prusti/:${PATH}"
