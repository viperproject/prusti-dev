# -*- mode: ruby -*-
# vi: set ft=ruby :

# All Vagrant configuration is done below. The "2" in Vagrant.configure
# configures the configuration version (we support older styles for
# backwards compatibility). Please don't change it unless you know what
# you're doing.
Vagrant.configure("2") do |config|
  # The most common configuration options are documented and commented below.
  # For a complete reference, please see the online documentation at
  # https://docs.vagrantup.com.

  # Every Vagrant development environment requires a box. You can search for
  # boxes at https://vagrantcloud.com/search.
  config.vm.box = "ubuntu/bionic64"

  # Disable automatic box update checking. If you disable this, then
  # boxes will only be checked for updates when the user runs
  # `vagrant box outdated`. This is not recommended.
  config.vm.box_check_update = true

  # Create a forwarded port mapping which allows access to a specific port
  # within the machine from a port on the host machine. In the example below,
  # accessing "localhost:8080" will access port 80 on the guest machine.
  # NOTE: This will enable public access to the opened port
  config.vm.network "forwarded_port", guest: 8080, host: 23438

  # Create a forwarded port mapping which allows access to a specific port
  # within the machine from a port on the host machine and only allow access
  # via 127.0.0.1 to disable public access
  # config.vm.network "forwarded_port", guest: 80, host: 8080, host_ip: "127.0.0.1"

  # Create a private network, which allows host-only access to the machine
  # using a specific IP.
  # config.vm.network "private_network", ip: "192.168.33.10"

  # Create a public network, which generally matched to bridged network.
  # Bridged networks make the machine appear as another physical device on
  # your network.
  # config.vm.network "public_network"

  # Share an additional folder to the guest VM. The first argument is
  # the path on the host to the actual folder. The second argument is
  # the path on the guest to mount the folder. And the optional third
  # argument is a set of non-required options.
  # config.vm.synced_folder "../data", "/vagrant_data"

  # Provider-specific configuration so you can fine-tune various
  # backing providers for Vagrant. These expose provider-specific options.
  # Example for VirtualBox:
  #
  config.vm.provider "virtualbox" do |vb|
    # Customize the amount of memory on the VM:
    vb.memory = "4096"
    vb.cpus = "2"
  end
  #
  # View the documentation for the provider you are using for more
  # information on available options.

  # Enable provisioning with a shell script. Additional provisioners such as
  # Puppet, Chef, Ansible, Salt, and Docker are also available. Please see the
  # documentation for more information about their specific syntax and use.
  config.vm.provision "shell", inline: <<-SHELL
    export PRUSTI_DEMO_DIR="/prusti"
    mkdir -p "$PRUSTI_DEMO_DIR"

    apt-get update
    apt-get dist-upgrade -y

    # Install dependencies.
    curl -sS https://dl.yarnpkg.com/debian/pubkey.gpg | apt-key add -
    echo "deb https://dl.yarnpkg.com/debian/ stable main" | tee /etc/apt/sources.list.d/yarn.list
    apt-get update && apt-get install -y yarn
    apt-get install -y libssl-dev build-essential fish pkg-config
    curl -sL https://deb.nodesource.com/setup_10.x | bash -
    apt-get update && apt-get install -y nodejs

    # Install Docker.
    apt-get install -y \
        apt-transport-https \
        ca-certificates \
        curl \
        gnupg-agent \
        software-properties-common
    curl -fsSL https://download.docker.com/linux/ubuntu/gpg | apt-key add -
    apt-key fingerprint 0EBFCD88
    add-apt-repository \
       "deb [arch=amd64] https://download.docker.com/linux/ubuntu \
       $(lsb_release -cs) \
       stable"
    apt-get update
    apt-get install -y docker-ce docker-ce-cli containerd.io

    # Install Rust.
    curl https://sh.rustup.rs -sSf | sh -s -- -y
    source $HOME/.cargo/env

    # 1. Build Prusti
    cd "$PRUSTI_DEMO_DIR"
    git clone /vagrant prusti
    cd prusti
    make build-docker-images
    export RUSTUP_TOOLCHAIN=$(cat "$PRUSTI_DEMO_DIR/prusti/rust-toolchain")
    rustup toolchain install ${RUSTUP_TOOLCHAIN}
    rustup default ${RUSTUP_TOOLCHAIN}

    # 2. Build `rust-playground`
    cd "$PRUSTI_DEMO_DIR"
    git clone https://github.com/integer32llc/rust-playground.git
    cd rust-playground
    git checkout f103d06cfb4c96ca6055ae9f4b16ca5cca03c852
    cd ui
    sed -e 's/"256m"/"2048m"/g' -i src/sandbox.rs
    sed -e 's/println!("Hello, world!");/unreachable!();/g' \
        -e 's/fn main/extern crate prusti_contracts;\nfn main/g' \
        -i frontend/reducers/code.ts
    cargo build --release
    cd frontend
    yarn
    yarn run build:production

    # 3. Create service.
    cp /vagrant/playground.service /etc/systemd/system/playground.service
    service playground start
    systemctl enable playground.service

  SHELL
end
