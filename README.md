# Prusti

[![Build Status][build_badge]][build_status]
[![License: MPL-2.0](https://img.shields.io/crates/l/prusti.svg)](#license)

[Development documentation][documentation]

Prusti is a Rust front-end for the [Viper verification
infrastructure](http://www.pm.inf.ethz.ch/research/viper.html).

[build_badge]: https://travis-ci.org/viperproject/prusti.svg
[build_status]: https://travis-ci.org/viperproject/prusti
[documentation]: https://viperproject.github.io/prusti-dev/prusti/


## Debugging

You can specify the log level as follows:

```bash
make LOG_LEVEL=trace run
```


## Demo: `rust-playground`

Choose a folder in which to run the demo
```bash
export DEV_DIR = "/tmp/prusti-demo"
mkdir -p $DEV_DIR
```

### 1. Build Prusti
```bash
cd $DEV_DIR
git clone git@github.com:viperproject/prusti.git
cd prusti/docker
docker build -t rust-nightly .
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
TMPDIR=/tmp/playground \
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
