# Providing Flags

Flags can be set in one of four ways, in increasing order of priority:

1. Provided lowercase in a `Prusti.toml` file in the current working directory (for example, `check_overflows` for the [`CHECK_OVERFLOWS`](flags.md#check_overflows) flag).
2. Provided lowercase in a TOML file with the path in the environment variable `PRUSTI_CONFIG`.
3. Provided individually as environment variables with the prefix `PRUSTI_` (for example, `PRUSTI_ASSERT_TIMEOUT` for the [`ASSERT_TIMEOUT`](flags.md#assert_timeout) flag).
4. Provided individually as command-line arguments to Prusti with the prefix `-P` (for example, `-Pprint_desugared_specs` for the [`PRINT_DESUGARED_SPECS`](flags.md#print_desugared_specs) flag).
