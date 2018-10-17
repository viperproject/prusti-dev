Prusti-dev
==========

[![Build Status][build_badge]][build_status]


Workspace project containing all Prusti sub-projects.

[build_badge]: https://travis-ci.org/viperproject/prusti-dev.svg
[build_status]: https://travis-ci.org/viperproject/prusti-dev


Documentation
-------------

[Development documentation](https://viperproject.github.io/prusti-dev/)

Modules:

- [jni-gen](https://viperproject.github.io/prusti-dev/jni_gen/)
- [viper-sys](https://viperproject.github.io/prusti-dev/viper_sys/)
- [viper](https://viperproject.github.io/prusti-dev/viper/)
- [prusti-viper](https://viperproject.github.io/prusti-dev/prusti_viper/)
- [prusti-utils](https://viperproject.github.io/prusti-dev/prusti_utils/)
- [prusti-interface](https://viperproject.github.io/prusti-dev/prusti_interface/)
- [prusti](https://viperproject.github.io/prusti-dev/prusti/)


Option (a): local development
-----------------------------

- Install the `viper` package.

    ```bash
    wget -q -O - https://pmserver.inf.ethz.ch/viper/debs/xenial/key.asc | sudo apt-key add -
    echo 'deb http://pmserver.inf.ethz.ch/viper/debs/xenial /' | sudo tee /etc/apt/sources.list.d/viper.list
    sudo apt-get update  
    sudo apt-get install viper
    ```

- Install Java 8 or a later version.

    ```bash
    sudo apt-get install default-jre
    ```

- Check that the `JAVA_HOME` env var is set. If not, set it.

    ```bash
    export JAVA_HOME=/usr/lib/jvm/default-java
    ```

- Set the `LD_LIBRARY_PATH` environment variable
	This depends on 
	
    ```bash
    export LD_LIBRARY_PATH="$JAVA_HOME/jre/lib/amd64/server/"
	```

    ```bash
    export LD_LIBRARY_PATH="$JAVA_HOME/lib/server/"
    ```

    Note: make sure that `LD_LIBRARY_PATH` does not contain empty
    segments because it can cause a crash with a “multiple inputs
    provided” error.

- Install Rustup

	```bash
	curl https://sh.rustup.rs -sSf | sh
	```

- Install the Rust compiler

    ```bash
    rustup toolchain install nightly-2018-06-27
    ```

- Download this Prusti repository and move to the `prusti-dev` folder

	```bash
	git clone <prusti-repository-url>
	cd prusti-dev
	```

- Set the Rust compiler version for this folder

    ```bash
    rustup override set nightly-2018-06-27
    ```

- Make sure to have some dependencies

	```bash
	sudo apt-get install build-essential pkg-config gcc libssl-dev
	```

- You can now build Prusti

    ```bash
    cargo build --all
    ```


Option (b): demo with `rust-playground`
---------------------------------------

Choose a folder in which to run the demo
```bash
export DEV_DIR="/tmp/prusti-demo"
mkdir -p $DEV_DIR
```

### 1. Build Prusti
```bash
cd $DEV_DIR
git clone git@github.com:viperproject/prusti-dev.git
docker build --no-cache -t rust-nightly -f docker/Dockerfile .
```

### 2. Build `rust-playground`
```bash
cd $DEV_DIR
git clone git@github.com:integer32llc/rust-playground.git
cd rust-playground/ui
cargo build --release
cd frontend
yarn
yarn run build
```

### 3. Start demo
```bash
cd $DEV_DIR/rust-playground/ui
TMPDIR=/tmp \
RUST_LOG=debug \
PLAYGROUND_UI_ADDRESS=0.0.0.0 \
PLAYGROUND_UI_PORT=8080 \
PLAYGROUND_UI_ROOT=$PWD/frontend/build \
PLAYGROUND_GITHUB_TOKEN="" \
./target/release/ui
```

### 4. Use demo

Visit <http://localhost:8080/>

Select "Nightly channel".

Start with the following program:
```rust
extern crate prusti_contracts;

fn main() {
    unreachable!();
}
```

Click on "Build" and watch at the compiler messages.
