# IDE integration

## Warnings as Errors

Prusti uses rather strict code style settings, producing errors for unnecessary code like unused imports. Although this is useful (especially since incremental builds can hide warnings that still apply), it is often obstructive while  actively working on the codebase. These linter errors can be treated as  warnings instead of errors by providing a compiler flag:

 - With a command-line argument to Rust: `--cap-lints warn`
 - With an environment variable: `RUSTFLAGS='--cap-lints warn'`

## VS Code

Assuming VS Code is in `PATH`, it can be launched directly with the correct environment variables set up using `x.py`:

```bash
$ ./x.py ide
```

Any additional arguments are passed to VS Code.

## IntelliJ Rust

When using the [Rust Plugin for IntelliJ](https://intellij-rust.github.io/), a lot of spurious errors may be found in the code. This is because Prusti uses a custom toolchain (set in the `rust-toolchain` file), which makes the plugin fail to load the [prelude definitions](https://doc.rust-lang.org/std/prelude/). The issue is tracked in the `intellij-rust` repository [here](https://github.com/intellij-rust/intellij-rust/issues/4930).

A temporary workaround is to set the path to the toolchain in use in IntelliJ settings.

 - Inside the Prusti directory, run `rustup which cargo` in the terminal.
 - Go to Preferences > Languages & Frameworks > Rust.
 - Change the standard library location to the standard library directory inside the Rust toolchain.

As an example, if `rustup which cargo` returned `/Users/example/.rustup/toolchains/nightly-2020-08-17-x86_64-apple-darwin/bin/cargo`, the standard library directory is `/Users/example/.rustup/toolchains/nightly-2020-08-17-x86_64-apple-darwin/lib/rustlib/src/rust/library`.
