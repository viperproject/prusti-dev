# Providing Flags

Flags can be set in one of four ways, in increasing order of priority:

1. Provided individually as environment variables with the prefix `DEFAULT_PRUSTI_` (for example, `DEFAULT_PRUSTI_CACHE_PATH` for the [`CACHE_PATH`](flags.md#cache_path) flag).
> NOTE: One should only use this to change the default value of flags, such that this can be overridden by a config file

2. Provided lowercase in a file ([allowed formats](https://docs.rs/config/latest/config/enum.FileFormat.html)) with the path in the environment variable `PRUSTI_CONFIG` (for example, `check_overflows` for the [`CHECK_OVERFLOWS`](flags.md#check_overflows) flag). This path defaults to `./Prusti.toml` if the environment variable is not set.

3. Provided individually as environment variables with the prefix `PRUSTI_` (for example, `PRUSTI_ASSERT_TIMEOUT` for the [`ASSERT_TIMEOUT`](flags.md#assert_timeout) flag).

4. Provided individually as command-line arguments to Prusti with the prefix `-P` (for example, `-Pprint_desugared_specs` for the [`PRINT_DESUGARED_SPECS`](flags.md#print_desugared_specs) flag).
