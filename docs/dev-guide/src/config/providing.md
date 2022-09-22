# Providing Flags

Flags can be set in one of four ways, in increasing order of priority:

1. Provided individually as environment variables with the prefix `DEFAULT_PRUSTI_` (for example, `DEFAULT_PRUSTI_CACHE_PATH` for the [`CACHE_PATH`](flags.md#cache_path) flag).
> **Note:** One should only use this to change the default value of flags, such that this can be overridden by a config file

2. Provided lowercase in a `Prusti.toml` file ([allowed formats](https://docs.rs/config/latest/config/enum.FileFormat.html), e.g. `check_overflows = true` for the [`CHECK_OVERFLOWS`](flags.md#check_overflows) flag). Prusti searches for a `Prusti.toml` depending on how it is run:<a name="flags-2"></a>

    - As `cargo prusti` (on an entire crate): in the [`CARGO_MANIFEST_DIR`](https://doc.rust-lang.org/cargo/reference/environment-variables.html#environment-variables-cargo-sets-for-crates), i.e. next to the crate's `Cargo.toml`
    - As `prusti-rustc` (on a single Rust file): in the current working directory

3. Provided individually as environment variables with the prefix `PRUSTI_` (for example, `PRUSTI_ASSERT_TIMEOUT` for the [`ASSERT_TIMEOUT`](flags.md#assert_timeout) flag).

4. Provided individually as command-line arguments to Prusti with the prefix `-P` (for example, `-Pprint_desugared_specs` for the [`PRINT_DESUGARED_SPECS`](flags.md#print_desugared_specs) flag).

## Multi-crate Cargo Prusti Projects

Setting flags becomes slightly more complicated when Prusti is run on multiple crates as `cargo prusti`; e.g. which `Prusti.toml` file will be used. Though overriding priority as above remains the same, the three possible approaches to providing flags all behave differently, in particular depending on flag [Category](flags.md#list-of-configuration-flags).

### Environment Variables

The environment persists throughout compilation, therefore all flags set through the `DEFAULT_PRUSTI_` or `PRUSTI_` will apply to all crates, and flags of both Category A and B. For example setting `PRUSTI_CHECK_OVERFLOWS=false` will disable overflow checks in all dependencies, even if they try to override this with a `Prusti.toml` file.

### Prusti Config File

A `Prusti.toml` is optionally loaded from the current working directory prior to compilation. This file is used to configure flags in Category B _only_ and these flags apply to the entire compilation.

Then, as each individual crate is checked (from the roots of the dependency tree) a `Prusti.toml` is optionally loaded from the directory where the crate's corresponding `Cargo.toml` is located. This file is used to configure flags in Category A _only_ — it would not make sense to set e.g. [`NO_VERIFY_DEPS`](flags.md#no_verify_deps) in a dependency since all of its dependencies have already been verified.

Therefore, when publishing a `lib` crate to git/crates.io one can configure Category A flags by including a `Prusti.toml` file next to their `Cargo.toml`.

> **Note:** Currently cargo does not track `Prusti.toml` files as a [dependency](https://doc.rust-lang.org/cargo/guide/build-cache.html#dep-info-files), therefore if it's the only file that changed in a crate you may need to run `cargo clean -p <crate>` to force reverification

The `Prusti.toml` used to load Category B flags at the start and the one used to load Category A flags at the end for the root crate will often be one and the same because `cargo prusti` is typically run from the root crate's directory. This can be changed by providing the [`--manifest-path` flag](https://doc.rust-lang.org/cargo/commands/cargo-check.html#manifest-options).

### Commandline Arguments

Prusti `-P` flags can be provided after a `--` (e.g. `cargo prusti -- -Pcargo_command=build`). Currently flags from Category B _only_ are supported; providing a flag in Category A this way will be ignored.

Flags to cargo are provided in the [regular way](https://doc.rust-lang.org/cargo/commands/cargo-check.html#options) (e.g. `cargo prusti --features foo`).
