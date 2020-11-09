# Verification Pipeline

At a high level, Prusti is a plugin to the [Rust compiler](https://rustc-dev-guide.rust-lang.org/) that converts Rust code enriched with Prusti specifications into [Viper code](https://viper.ethz.ch), verifies the code with an external verifier, and then reports the results back to the user.

This chapter summarizes the steps that take place when the user runs Prusti on a given Rust file. The steps are described in greater detail in the subsequent sections. Although we present the steps in separate “stages”, this distinction only exists for the purposes of this guide, and is not clearly mirrored in the codebase.

1. [Binary stage](binary.md)
    - The user invokes the binary `prusti-rustc <file.rs>`.
    - The binary sets up important environment variables, then invokes `prusti_driver`.
2. [Rust compilation stage](rust.md)
    - `prusti_driver` registers callbacks and calls the Rust compiler.
    - The compiler expands all procedural macros, which includes the specifications.
    - The compiler does the type-checking.
    - The Prusti callback is called.
3. [Prusti processing stage](prusti.md)
    - The [MIR](https://rustc-dev-guide.rust-lang.org/mir/index.html) of functions that should be checked is obtained.
    - MIR is encoded into VIR - Prusti's intermediate representation.
    - VIR is enriched with `fold`/`unfold` statements and other ghost code.
    - VIR is simplified and optimized.
4. [Viper verification stage](viper.md)
    - (With Prusti server only) Send VIR to the server.
    - VIR is encoded into Viper.
    - The Viper verifier is called and the results are obtained.
    - (With Prusti server only) Send verification results back to the client.
5. [Reporting stage](report.md)
    - The Prusti client reports compilation and verification errors.
