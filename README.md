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


Build for local development
---------------------------

- Install the `viper` package.

    ```bash
    wget -q -O - https://pmserver.inf.ethz.ch/viper/debs/xenial/key.asc | sudo apt-key add -
    echo 'deb http://pmserver.inf.ethz.ch/viper/debs/xenial /' | sudo tee /etc/apt/sources.list.d/viper.list
    sudo apt-get update  
    sudo apt-get install viper
    ```

- Install Java 8 or a later version.

    ```bash
    sudo apt-get install default-jdk
    ```

- Install Rustup

	```bash
	curl https://sh.rustup.rs -sSf | sh
	```

- Install the Rust compiler (the exact compiler version is stored in the rust-toolchain file)

    ```bash
    rustup toolchain install $(cat rust-toolchain)
    ```

- Install the dependencies required by some Rust libraries

	```bash
	sudo apt-get install build-essential pkg-config gcc libssl-dev
	```

- Download this Prusti repository and move to the `prusti-dev` folder

	```bash
	git clone "<url-of-prusti-repository>"
	cd prusti-dev
	```

- You can now compile Prusti

    ```bash
    make build
    ```

- Make sure that the tests are passing

    ```bash
    make test
    ```

- To run Prusti and verify a program there are two options:

    ```bash
    make run RUN_FILE=path/to/the/program_to_be_verified.rs
    ```

	or

    ```bash
    ./docker/prusti path/to/the/program_to_be_verified.rs
    ```

- To see examples of programs with annotation, look into the `prusti/tests/verify/pass` folder.

- Install commands for the evaluation:

	```bash
	sudo apt-get install jq
	```

Demo with `rust-playground`
---------------------------

If you have [Vagrant](https://www.vagrantup.com/) installed, just run
``make demo`` and open
http://localhost:23438/?version=nightly&mode=debug&edition=2018.
Otherwise, you can follow the instructions below.

Choose a folder in which to run the demo
```bash
export PRUSTI_DEMO_DIR="/tmp/prusti-demo"
mkdir -p "$PRUSTI_DEMO_DIR"
```

### 1. Build Prusti
```bash
cd "$PRUSTI_DEMO_DIR"
git clone "<url-of-prusti-repository>"
make build-docker-images
```

### 2. Build `rust-playground`
```bash
cd "$PRUSTI_DEMO_DIR"
git clone git@github.com:integer32llc/rust-playground.git
cd rust-playground
git checkout f103d06cfb4c96ca6055ae9f4b16ca5cca03c852
cd ui
cargo build --release
cd frontend
yarn
yarn run build:production
```

### 3. Start demo
```bash
cd "$PRUSTI_DEMO_DIR/rust-playground/ui"
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

Write with the following program:
```rust
extern crate prusti_contracts;

fn main() {
    unreachable!();
}
```

Click on "Build" and watch at the compiler and verifier messages.
