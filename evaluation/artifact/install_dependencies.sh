#/bin/bash


# I

set -x
set -v

export DEBIAN_FRONTEND=noninteractive

apt-get update
apt-get install -y \
    build-essential \
    locales \
    file \
    curl \
    wget \
    git \
    python2.7 \
    cmake
apt-get clean

export RUSTUP_HOME=/usr/local/rustup
export CARGO_HOME=/usr/local/cargo
export PATH=/usr/local/cargo/bin:$PATH

# Install Rust.
mkdir -p /tmp/rust
cd /tmp/rust
wget -q -c https://sh.rustup.rs -O install.sh
chmod 755 install.sh
./install.sh -y --no-modify-path --default-toolchain nightly-2018-06-27
rm -rf /tmp/rust

# Install Prusti prerequisites.
wget -q -O - https://pmserver.inf.ethz.ch/viper/debs/xenial/key.asc | apt-key add -
echo "deb http://pmserver.inf.ethz.ch/viper/debs/xenial /" | tee /etc/apt/sources.list.d/viper.list
apt-get update
apt-get install -y \
    default-jre \
    pkg-config \
    libssl-dev \
    viper
apt-get clean
export JAVA_HOME="/usr/lib/jvm/default-java"
export LD_LIBRARY_PATH="$JAVA_HOME/jre/lib/amd64/server/"
