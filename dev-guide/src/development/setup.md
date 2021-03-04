# Setup

This section details the setup required before Prusti can be built from source.

## Prerequisites

 - [`rustup`](https://rustup.rs/)
 - [Python 3](https://www.python.org/downloads/) (for [`x.py`](#xpy))

## `x.py`

`x.py` is a Python script that provides a convenient wrapper for a Prusti development setup. It can be initialized by running:

```bash
$ ./x.py setup
```

The script will perform the following steps:

 1. (Ubuntu only) Installs the [native dependencies](#native-dependencies).
    - On other OS (including non-Ubuntu Linux distributions) this step has to be performed manually.
 2. Downloads and extracts the latest [Viper tools](#viper-tools).
 3. Sets up [the Rust toolchain](#rustup-setup).

Steps 1 and 2 can be skipped by adding the `--rustup-only` argument to the command line. `--dry-run` can be used to prevent any shell commands from actually running, only printing them to the terminal.

The `setup` step should be repeated if the Rust toolchain version changes, or if the native dependencies or Viper tools need to be updated.

## Native dependencies

### Linux

On a Linux-based OS, the required libraries are:

 - `build-essential`
 - `pkg-config`
 - `wget`
 - `gcc`
 - `libssl-dev`
 - `openjdk-11-jdk`

### macOS

On macOS, [Java JDK 11](https://www.oracle.com/java/technologies/javase-downloads.html) is required.

## Viper tools

[Viper tools](http://viper.ethz.ch/downloads/) are required by Prusti. Extracting the appropriate version into a directory called `viper_tools` in the project root allows `x.py` to automatically locate the Viper libraries and the Z3 solver.

## `rustup` setup

Rust versions and components are managed with `rustup`. The toolchain version in use is listed in the [`rust-toolchain`](https://github.com/viperproject/prusti-dev/blob/master/rust-toolchain) file. Additional components used are:

 - `rust-src`
 - `rustc-dev`
 - `llvm-tools-preview`
 - `rustfmt` (optional)

## Using locally built version in Prusti Assistant

**Note:** These instructions were tested only on Ubuntu.

To use the locally compiled version in Prusti Assistant, make sure to build Prusti in release mode:

```bash
./x.py build --release
```

Add necessary symlinks to the release directory:

```bash
ln -s $(pwd)/viper_tools $(pwd)/target/release/
ln -s $(pwd)/rust-toolchain $(pwd)/target/release/
```

Open VS Code and its settings change as follows:

 - Set `prusti-assistant.buildChannel` to `Local`.
 - Set `prusti-assistant.localPrustiPath` to `<prusti-dev-dir>/target/release/`.

Now, you should be able to verify Rust programs with a locally built version of Prusti.
