FROM fpoli/prusti-base:latest

RUN git clone https://github.com/viperproject/prusti-dev/ /tmp/prusti-dev && \
	cd /tmp/prusti-dev && \
	make release && \
	mkdir -p /usr/local/prusti/lib && \
	cp rust-toolchain /usr/local/prusti/rust-toolchain && \
	cp target/release/cargo-prusti /usr/local/prusti/cargo-prusti && \
	cp target/release/prusti-rustc /usr/local/prusti/prusti-rustc && \
	cp target/release/prusti-driver /usr/local/prusti/prusti-driver && \
	cp target/release/libprusti_contracts.rlib /usr/local/prusti/libprusti_contracts.rlib

RUN cd /tmp/prusti-dev && \
	cp ./bin/* /usr/local/bin

RUN rm -rf /tmp/prusti-dev

# Prepare env variables to run Prusti
ENV RUSTC_WRAPPER /usr/local/bin/prusti

# Continue compilation after the verification succeeds
ENV PRUSTI_FULL_COMPILATION true
