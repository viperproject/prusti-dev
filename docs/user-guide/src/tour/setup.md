# Setup

To get started, you can use an existing Rust project or create a new one with Cargo:

```sh
cargo new prusti_tutorial
```
Then you can change the current working directory to the project's directory:
```sh
cd ./prusti_tutorial/
```


To use the additional syntax used for verification with Prusti, you need to add the [prusti_contracts](https://docs.rs/prusti-contracts/latest/prusti_contracts/) crate to your project. If you have at least Cargo version 1.62.0, you can use this command to add the dependency:
```sh
cargo add prusti-contracts
```
For older versions of Rust, you can manually add the dependency in your Cargo.toml file:
```toml
[dependencies]
prusti-contracts = "0.1.2"
```


To use prusti-contracts in a Rust file, just add the following line:
```rust,ignore
use prusti_contracts::*;
```


To simplify the tutorial, overflow checks by Prusti will be disabled. To do that, create a file called `Prusti.toml` in your projects root directory (where `Cargo.toml` is located).
In this file, you can set [configuration flags](https://viperproject.github.io/prusti-dev/dev-guide/config/flags.html) used by Prusti. To disable overflow checking, add the following line:
```toml
check_overflows = false
```

TODO:
- nightly compiler needed(?)
- mention how to run Prusti on the created project
- mention that strings are not supported (remove print from generated main fn)