# Prusti

Prusti is a Rust front-end for the [Viper verification
infrastructure](http://www.pm.inf.ethz.ch/research/viper.html).


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
docker build --no-cache -t rust-nightly .
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
