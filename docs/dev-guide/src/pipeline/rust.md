# Rust compilation stage

- `prusti_driver` registers callbacks and calls the Rust compiler.
- The compiler expands all [procedural macros](../macros.md), which includes the specifications.
- The compiler does the type-checking.
- The Prusti callback is called.

In this stage, the actual Rust compiler is invoked to make sure the given code is valid Rust code, both syntactically and semantically. Prusti integrates with the Rust compiler using [`rustc_driver`](https://rustc-dev-guide.rust-lang.org/rustc-driver.html). This allows running the Rust compiler with [callbacks](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_driver/trait.Callbacks.html) triggered when important stages of processing are completed. In Prusti, we are interested in two stages:

 - [`prusti/src/callbacks.rs` - `PrustiCompilerCalls::after_expansion`](https://github.com/viperproject/prusti-dev/blob/f6850c5036c4a85c8812b46eed8ac472ca95fe25/prusti/src/callbacks.rs#L58) - for debugging and unit testing purposes, it is useful to see the Rust AST after the Prusti specifications are processed.
 - [`prusti/src/callbacks.rs` - `PrustiCompilerCalls::after_analysis`](https://github.com/viperproject/prusti-dev/blob/f6850c5036c4a85c8812b46eed8ac472ca95fe25/prusti/src/callbacks.rs#L89) - once the type checking is done and the code is determined to be type safe. Code that is syntactically invalid or has type errors is not relevant for Prusti applications.
