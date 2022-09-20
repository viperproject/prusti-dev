# Providing Flags

Flags can be set in one of four ways, in increasing order of priority:

1. Provided individually as environment variables with the prefix `DEFAULT_PRUSTI_` (for example, `DEFAULT_PRUSTI_CACHE_PATH` for the [`CACHE_PATH`](flags.md#cache_path) flag).
> NOTE: One should only use this to change the default value of flags, such that this can be overridden by a config file

2. Provided lowercase in a file ([allowed formats](https://docs.rs/config/latest/config/enum.FileFormat.html)) with the path in the environment variable `PRUSTI_CONFIG` (for example, `check_overflows` for the [`CHECK_OVERFLOWS`](flags.md#check_overflows) flag). This path defaults to `./Prusti.toml` if the environment variable is not set.<a name="flags-2"></a>

3. Provided individually as environment variables with the prefix `PRUSTI_` (for example, `PRUSTI_ASSERT_TIMEOUT` for the [`ASSERT_TIMEOUT`](flags.md#assert_timeout) flag).

4. Provided individually as command-line arguments to Prusti with the prefix `-P` (for example, `-Pprint_desugared_specs` for the [`PRINT_DESUGARED_SPECS`](flags.md#print_desugared_specs) flag).

## Multi-crate Cargo Prusti Projects

Setting flags becomes slightly more complicated when Prusti is run on multiple crates as `cargo prusti` (e.g. which `Prusti.toml` file will be used). The three possible approaches to providing flags all behave differently.

### Environment Variables

The environment persists throughout compilation, therefore any flags set through the `DEFAULT_PRUSTI_` or `PRUSTI_` will apply to both the root crate and all dependencies. For example setting `CHECK_OVERFLOWS=false` will disable overflow checks in all dependencies, even if they try to override this with a `Prusti.toml` file.

### Prusti Config File

A Prusti config file is loaded per crate compiled, if a relative path is specified (e.g. the default `./Prusti.toml`) then the file loaded depends on the current working directory when compiling the crate. Cargo sets the working directory for each crate as follows:

1. If the current crate is the (final) root crate, then use the directory from which `cargo prusti` was launched. Note: this case will never apply for workspace projects.

2. If the current crate is in a subdirectory of the root crate/workspace, then use the directory from which `cargo prusti` was launched. Note: this means that any `Prusti.toml` in this subdirectory will be ignored!

3. Else (the crate lives in an unrelated directory or was downloaded from git/crates.io to such a directory) use the directory of this dependency crate. Therefore (with the default `PRUSTI_CONFIG=./Prusti.toml`) a `Prusti.toml` placed next to the `Cargo.toml` of such a crate will load flags as expected.

However, this only applies to flags in Category A. All other flags (in Categories B and C) are loaded from the Prusti config file relative to the directory from which `cargo prusti` was launched and then apply to the entire compilation; it would not make sense to set e.g. [`NO_VERIFY_DEPS`](flags.md#no_verify_deps) in the `Prusti.toml` of a dependency (especially since crates are checked bottom up).

### Commandline Arguments

Flags to cargo are provided in the regular way (e.g. `cargo prusti --features foo`). Prusti `-P` flags can be provided after a `--` (e.g. `cargo prusti -- -Pcargo_command=build`). Only flags in Categories B and C are currently supported; providing a flag in Category A this way will be ignored.
