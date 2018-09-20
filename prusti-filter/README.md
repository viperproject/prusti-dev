Prusti-filter
=============

Lists all the functions and methods in a crate that can be verified in Prusti.

Note: this crate does not verify code.

Usage
-----

1. Build `prusti-filter` with `cargo build`. 
2. Move to the folder containing the source code of a crate of interest.
3. In that folder, run `cargo clean`.
4. Always in that folder, execute the `script/cargo-build.rs` script of this `prusti-filter` crate.
5. The script will list which functions/methods are supported by Prusti.
