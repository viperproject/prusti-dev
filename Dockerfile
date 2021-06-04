FROM ubuntu:18.04
MAINTAINER Federico Poli "federico.poli@inf.ethz.ch"

ENV DEBIAN_FRONTEND noninteractive

# Install prerequisites
RUN apt-get update && \
    apt-get install -y \
        build-essential \
        cmake \
        curl \
        default-jdk \
        file \
        gcc \
        git \
        libssl-dev \
        locales \
        mono-complete \
        pkg-config \
        python3 \
        sudo \
        unzip \
        wget \
    && \
    rm -rf /var/lib/apt/lists/*

# Set up locale
RUN locale-gen en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

# Set up Java
ENV JAVA_HOME /usr/lib/jvm/default-java
ENV LD_LIBRARY_PATH $JAVA_HOME/lib/server/

# Install Rust
ADD rust-toolchain /tmp/rust-toolchain
RUN CHANNEL=$(cat /tmp/rust-toolchain | grep channel | cut -d'"' -f2) && \
    echo "Rust toolchain: $CHANNEL" && \
    curl https://sh.rustup.rs -sSf \
        | sh -s -- -y --profile minimal --no-modify-path --default-toolchain "$CHANNEL"
ENV PATH /root/.cargo/bin:$PATH

# Set up Prusti
ADD . /opt/prusti-dev
RUN cd /opt/prusti-dev && \
    ./x.py setup && \
    rm -rf /var/lib/apt/lists/*

# Build and install Prusti
RUN cd /opt/prusti-dev && \
    ./x.py build --release && \
    mkdir -p /usr/local/prusti/deps/ && \
	cp -r viper_tools/ /usr/local/prusti/ && \
    cp rust-toolchain /usr/local/prusti/ && \
    cp target/release/prusti-driver /usr/local/prusti/ && \
    cp target/release/prusti-server-driver /usr/local/prusti/ && \
    cp target/release/prusti-server /usr/local/prusti/ && \
    cp target/release/prusti-rustc /usr/local/prusti/ && \
    cp target/release/cargo-prusti /usr/local/prusti/ && \
    cp target/release/libprusti_contracts.rlib /usr/local/prusti/ && \
    cp target/release/deps/libprusti_contracts_internal-* /usr/local/prusti/deps/ && \
    rm -rf target
ENV PATH "/usr/local/prusti/:${PATH}"

# Check on a few crates that Prusti works
WORKDIR /root
RUN cargo new good-example && \
    cd good-example && \
    sed -i '1s/^/use prusti_contracts::*;\n/;s/println.*$/assert!(true);/' src/main.rs && \
    echo 'prusti-contracts = { path = "/opt/prusti-dev/prusti-contracts" }' >> Cargo.toml && \
    cargo build && cargo clean && \
    cargo prusti && cargo clean
RUN cargo new bad-example && \
    cd bad-example && \
    sed -i '1s/^/use prusti_contracts::*;\n/;s/println.*$/assert!(false);/' src/main.rs && \
    echo 'prusti-contracts = { path = "/opt/prusti-dev/prusti-contracts" }' >> Cargo.toml && \
    cargo build && cargo clean && \
    ! cargo prusti && cargo clean
