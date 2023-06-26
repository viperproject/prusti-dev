# Setup

To get started, you can use an existing Rust project or create a new one with [Cargo](https://doc.rust-lang.org/cargo/):

```sh
cargo new prusti_tutorial
```
Then you can change the current working directory to the project's directory:
```sh
cd ./prusti_tutorial/
```


To use the additional syntax used for verification with Prusti, you need to add the [`prusti-contracts`](https://crates.io/crates/prusti-contracts) crate to your project. If you have at least Cargo version 1.62.0, you can use this command to add the dependency:
```sh
cargo add prusti-contracts
```
For older versions of Rust, you can manually add the dependency in your Cargo.toml file:
```toml
[dependencies]
prusti-contracts = "0.1.6"
```

To use prusti-contracts in a Rust code file, just add the following line:
```rust,ignore
use prusti_contracts::*;
```


To simplify the tutorial, overflow checks by Prusti will be disabled. To do that, create a file called `Prusti.toml` in your project's root directory (where `Cargo.toml` is located).
In this file, you can set [configuration flags](https://viperproject.github.io/prusti-dev/dev-guide/config/flags.html) used by Prusti. To disable overflow checking, add the following line:
```toml
check_overflows = false
```

**Note**: Creating a new project will create a `main.rs` file containing a `Hello World` program. Since Prusti does not yet support Strings, verification will fail on `main.rs`. To still verify the code, remove the line `println!("Hello, world!");`.

<!-- TODO: link capabilities/limitations chapter (strings) -->

## Standard library annotations

Annotations for functions and types in the Rust standard library will be available in the [`prusti-std` crate](https://crates.io/crates/prusti-std) after [this PR](https://github.com/viperproject/prusti-dev/pull/1249) is merged.

Adding this crate works the same as for the `prusti-contracts` crate:
```sh
cargo add prusti-std
```
or:
```toml
[dependencies]
prusti-std = "0.1.6"
```
You do not need to import anything to use the annotations in this crate in a file.
