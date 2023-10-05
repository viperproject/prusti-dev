Test-crates
============

A tool to run and test Prusti on a set of popular Rust crates.

The tool is built upon [rustwide](https://github.com/rust-lang/rustwide). The `crates.csv` file contains the list of crates to test, specifying for each crate its name, version, and a "test kind" flag that configures how Prusti is tested.

Possible values for the test kind, strictly ordered from the most permissive to the most restrictive kind, are the following:
1. `Skip`: Completely ignore this crate.
1. `NoCrash`: Test that `cargo-prusti` does not crash nor generate "invalid" errors.
1. `NoErrors`: Test that `cargo-prusti` does not crash nor generate "internal/invalid" errors.
1. `NoErrorsWithUnreachableUnsupportedCode`: Test that `cargo-prusti` does not crash nor generate "internal/invalid" when the `allow_unreachable_unsupported_code` flag is set.

To make these tests fully reproducible one should also freeze the `Cargo.lock` in each crate. Without that, the dependencies used by the tested crate can change from time to time. In practice, this is usually not a big issue.
