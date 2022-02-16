# Binary stage

- The user invokes the binary `prusti-rustc <file.rs>`.
- The binary sets up important environment variables, then invokes `prusti_driver`.

This is a short stage responsible for setting up the correct environment variables for the Rust compiler and the Prusti-supporting libraries. To invoke `prusti-driver` correctly, the following arguments are set up:

 - `--sysroot`, pointing to the Rust sysroot where its libraries are stored.
 - `-L`, adding Prusti's `target/*/deps` directory into the library search path.
 - `--extern prusti_contracts=...` and `--extern prusti_contracts_internal=...`, specifying the path for the dynamic libraries containing the procedural macros for Prusti specifications.

> - [`prusti/src/bin/prusti-rustc.rs`](https://github.com/viperproject/prusti-dev/blob/143e673dc19b4c1363efade90ffee4f77641ec11/prusti/src/bin/prusti-rustc.rs)
