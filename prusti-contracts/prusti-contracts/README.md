Provides various macros and types needed for verification of a crate with Prusti. See the Prusti [user guide](https://prusti.github.io/prusti/user-guide/) or [GitHub page](https://github.com/prusti/prusti#readme) for more information.

When used without Prusti (e.g. with `cargo build`) this crate will be as transparent as possible and does not need to be removed from the dependencies. When running `cargo prusti` the `"prusti"` feature is _automatically_ enabled, resulting in the full expansion of the procedural macros this crate provides.
