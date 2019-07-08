FROM ubuntu:18.04
MAINTAINER Vytautas Astrauskas "vastrauskas@gmail.com"

ENV DEBIAN_FRONTEND noninteractive

# Install prerequisites
RUN apt-get update && \
    apt-get install -y \
        build-essential \
        cmake \
        curl \
        file \
        gcc \
        git \
        libssl-dev \
        locales \
        pkg-config \
        python \
        unzip \
        wget \
    && \
    rm -rf /var/lib/apt/lists/*

# Set up locale
RUN locale-gen en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

# Install Java
RUN apt-get update && \
    apt-get install -y default-jdk && \
    rm -rf /var/lib/apt/lists/*
ENV JAVA_HOME /usr/lib/jvm/default-java
ENV LD_LIBRARY_PATH $JAVA_HOME/lib/server/

# Install Rust
ARG RUST_TOOLCHAIN
RUN test -n "$RUST_TOOLCHAIN"
ENV RUST_TOOLCHAIN $RUST_TOOLCHAIN
ENV RUSTUP_HOME /usr/local/rustup
ENV CARGO_HOME /usr/local/cargo
ENV PATH /usr/local/cargo/bin:$PATH
# https://github.com/rust-lang-nursery/rustup.rs/issues/998
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --no-modify-path --default-toolchain "$RUST_TOOLCHAIN" && \
    rm -rf ~/.rustup/toolchains/*/share/doc

# Install Viper, with Mono for Carbon
RUN wget -q -O - https://pmserver.inf.ethz.ch/viper/debs/xenial/key.asc | apt-key add -
RUN echo "deb http://pmserver.inf.ethz.ch/viper/debs/xenial /" | tee /etc/apt/sources.list.d/viper.list
# A new release will trigger these lines to run again, forcing a new installation of Viper.
ADD https://pmserver.inf.ethz.ch/viper/debs/xenial/Packages /root/viper-xenial-packages.txt
RUN apt-get update && \
    apt-get install -y viper mono-complete && \
    rm -rf /var/lib/apt/lists/*
ENV Z3_EXE /usr/bin/viper-z3

WORKDIR /
