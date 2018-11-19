# Adapted version of the Docker image used for the Rust Playground.
FROM ubuntu:16.04
MAINTAINER Vytautas Astrauskas "vastrauskas@gmail.com"


ENV DEBIAN_FRONTEND noninteractive

# Install prerequisites.
RUN apt-get update && \
    apt-get install -y \
        build-essential \
        locales \
        file \
        curl \
        wget \
        git \
        python2.7 \
        cmake \
        && \
    apt-get clean

ENV RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    PATH=/usr/local/cargo/bin:$PATH

# Install Rust.
RUN bash <(curl https://sh.rustup.rs -sSf) -y --no-modify-path --default-toolchain "$(cat rust-toolchain)"

# Install Prusti prerequisites.
RUN wget -q -O - https://pmserver.inf.ethz.ch/viper/debs/xenial/key.asc | apt-key add -
RUN echo "deb http://pmserver.inf.ethz.ch/viper/debs/xenial /" | tee /etc/apt/sources.list.d/viper.list
RUN apt-get update && \
    apt-get install -y \
        default-jre \
        pkg-config \
        libssl-dev \
        viper \
        && \
    apt-get clean
ENV JAVA_HOME="/usr/lib/jvm/default-java"
ENV LD_LIBRARY_PATH="$JAVA_HOME/jre/lib/amd64/server/"

# Install Prusti.
RUN echo "TODO: Download prusti-dev in /tmp/prusti-dev"
ADD . /tmp/prusti-dev
RUN cd /tmp/prusti-dev && \
    cargo build --release && \
	mkdir -p /usr/local/prusti/lib && \
	cp rust-toolchain /usr/local/prusti/rust-toolchain && \
	cp target/release/prusti-driver /usr/local/prusti/prusti-driver && \
	cp target/release/libprusti.so /usr/local/prusti/libprusti.so && \
	cp target/release/libprusti_contracts.rlib /usr/local/prusti/libprusti_contracts.rlib
ADD docker/prusti /usr/local/bin/prusti
ADD docker/cargo-prusti /usr/local/bin/cargo-prusti
ENV RUSTC_WRAPPER "/usr/local/bin/prusti"

# Set up locale.
RUN locale-gen en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

# Mark container.
ENV RUST_CONTAINER 1

# Continue compilation after the verification succeeds
ENV PRUSTI_FULL_COMPILATION true

ADD docker/entrypoint.sh /root/
ENTRYPOINT ["/root/entrypoint.sh"]

# Set up workdir.
ENV USER=root
RUN cd / && \
    cargo new playground && \
    sed -i '1s/^/extern crate prusti_contracts;\n/;s/println.*$/assert!(true)/' /playground/src/main.rs
WORKDIR /playground

RUN cargo build && \
    cargo build --release && \
    rm src/*.rs
