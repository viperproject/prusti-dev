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
    ./install.sh -y --no-modify-path --default-toolchain nightly-2017-12-10 && \
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

# Set up locale.
RUN locale-gen en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

# Mark container.
ENV RUST_CONTAINER 1

# Set up workdir.
RUN cd / && \
    cargo new playground
WORKDIR /playground

RUN cargo build && \
    cargo build --release && \
    rm src/*.rs
