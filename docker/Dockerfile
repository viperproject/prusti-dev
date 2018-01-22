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
RUN mkdir -p /tmp/rust && \
    cd /tmp/rust && \
    wget -q -c https://sh.rustup.rs -O install.sh && \
    chmod 755 install.sh && \
    ./install.sh -y --no-modify-path --default-toolchain nightly-2018-01-21 && \
    rm -rf /tmp/rust

# Install NLL Rust.
RUN cd /tmp && \
    git clone https://github.com/nikomatsakis/rust.git rust-nll && \
    cd rust-nll && \
    git checkout nll-master && \
    git pull origin nll-master && \
    cp config.toml.example config.toml && \
    mkdir -p /rust-nll && \
    sed -e 's/#prefix = "\/usr\/local"/prefix = "\/rust-nll"/g' -i config.toml && \
    sed -e 's/#sysconfdir = "\/etc"/sysconfdir = "etc"/g' -i config.toml && \
    python2.7 ./x.py build && \
    python2.7 ./x.py install && \
    cd / && \
    rm -rf /tmp/*
ENV RUSTC=/rust-nll/bin/rustc

# Install Prusti prerequisites.
RUN wget -q -O - http://pmserver.inf.ethz.ch/viper/debs/xenial/key.asc | apt-key add -
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
RUN cd /tmp && \
    git clone https://github.com/viperproject/prusti.git prusti && \
    cd prusti && \
    cargo build --release && \
    mkdir -p /usr/lib/prusti && \
    cp target/release/libprusti.so /usr/lib/prusti && \
    rm -rf /tmp/*
ENV RUSTFLAGS="-L /usr/lib/prusti/ -Z mir-emit-validate=1 -Z extra-plugins=prusti -Z borrowck=mir -Z nll"

# Set up locale.
RUN locale-gen en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

# Mark container.
ENV RUST_CONTAINER 1

# Set up workdir.
ENV USER=root
RUN cd / && \
    cargo new playground
WORKDIR /playground

RUN cargo build && \
    cargo build --release && \
    rm src/*.rs
