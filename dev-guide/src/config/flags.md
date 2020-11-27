# Flags

Flags can be set in one of three ways, in increasing order of priority:

1. Provided in a `Prusti.toml` file in the current working directory.
2. Provided in a TOML file with the path in the environment variable `PRUSTI_CONFIG`.
3. Provided individually as environment variables with the prefix `PRUSTI_` (e.g. `PRUSTI_ASSERT_TIMEOUT` for the [`ASSERT_TIMEOUT`](#assert_timeout) flag).

| Name | Rust type | Default value |
| --- | --- | --- |
| [`ASSERT_TIMEOUT`](#assert_timeout) | `u64` | `10_000` |
| [`BE_RUSTC`](#be_rustc) | `bool` | `false` |
| [`CHECK_OVERFLOWS`](#check_overflows) | `bool` | `false` |
| [`CHECK_FOLDUNFOLD_STATE`](#check_foldunfold_state) | `bool` | `false` |
| [`CHECK_PANICS`](#check_panics) | `bool` | `true` |
| [`CONTRACTS_LIB`](#contracts_lib) | `String` | `""` |
| [`DELETE_BASIC_BLOCKS`](#delete_basic_blocks) | `Vec<String>` | `vec![]` |
| [`DISABLE_NAME_MANGLING`](#disable_name_mangling) | `bool` | `false` |
| [`DUMP_BORROWCK_INFO`](#dump_borrowck_info) | `bool` | `false` |
| [`DUMP_DEBUG_INFO`](#dump_debug_info) | `bool` | `false` |
| [`DUMP_PATH_CTXT_IN_DEBUG_INFO`](#dump_path_ctxt_in_debug_info) | `bool` | `false` |
| [`DUMP_REBORROWING_DAG_IN_DEBUG_INFO`](#dump_reborrowing_dag_in_debug_info) | `bool` | `false` |
| [`DUMP_VIPER_PROGRAM`](#dump_viper_program) | `bool` | `false` |
| [`ENABLE_VERIFY_ONLY_BASIC_BLOCK_PATH`](#enable_verify_only_basic_block_path) | `bool` | `false` |
| [`ENABLE_WHITELIST`](#enable_whitelist) | `bool` | `false` |
| [`ENCODE_UNSIGNED_NUM_CONSTRAINT`](#encode_unsigned_num_constraint) | `bool` | `false` |
| [`ERROR_ON_PARTIALLY_SUPPORTED`](#error_on_partially_supported) | `bool` | `false` |
| [`EXTRA_JVM_ARGS`](#extra_jvm_args) | `Vec<String>` | `vec![]` |
| [`EXTRA_VERIFIER_ARGS`](#extra_verifier_args) | `Vec<String>` | `vec![]` |
| [`FOLDUNFOLD_STATE_FILTER`](#foldunfold_state_filter) | `String` | `""` |
| [`FULL_COMPILATION`](#full_compilation) | `bool` | `false` |
| [`JSON_COMMUNICATION`](#json_communication) | `bool` | `false` |
| [`LOG`](#log) | `Option<String>` | `None` |
| [`LOG_DIR`](#log_dir) | `String` | `"./log/"` |
| [`LOG_STYLE`](#log_style) | `String` | `"auto"` |
| [`NO_VERIFY`](#no_verify) | `bool` | `false` |
| [`NUM_PARENTS_FOR_DUMPS`](#num_parents_for_dumps) | `u64` | `0` |
| [`QUIET`](#quiet) | `bool` | `false` |
| [`REPORT_SUPPORT_STATUS`](#report_support_status) | `bool` | `true` |
| [`SERVER_ADDRESS`](#server_address) | `Option<String>` | `None` |
| [`SERVER_MAX_CONCURRENCY`](#server_max_concurrency) | `Option<usize>` | `None` |
| [`SERVER_MAX_STORED_VERIFIERS`](#server_max_stored_verifiers) | `Option<usize>` | `None` |
| [`SIMPLIFY_ENCODING`](#simplify_encoding) | `bool` | `true` |
| [`SKIP_UNSUPPORTED_FEATURES`](#skip_unsupported_features) | `bool` | `false` |
| [`USE_MORE_COMPLETE_EXHALE`](#use_more_complete_exhale) | `bool` | `true` |
| [`VERIFY_ONLY_BASIC_BLOCK_PATH`](#verify_only_basic_block_path) | `Vec<String>` | `vec![]` |
| [`VERIFY_ONLY_PREAMBLE`](#verify_only_preamble) | `bool` | `false` |
| [`VIPER_BACKEND`](#viper_backend) | `String` | `"Silicon"` |
| [`WHITELIST`](#whitelist) | `Vec<String>` | `vec![]` |

## `ASSERT_TIMEOUT`

Maximum time (in milliseconds) for the verifier to spend on a single assertion. Set to `0` to disable timeout. Maps to the verifier command-line argument `--assertTimeout`.

## `BE_RUSTC`

When enabled, Prusti will behave like `rustc`.

## `CHECK_OVERFLOWS`

When enabled, binary operations and numeric casts will be checked for overflows. See [integer type encoding](../encoding/types.md#i-u-char).

## `CHECK_FOLDUNFOLD_STATE`

When enabled, additional, *slow*, checks for the `fold`/`unfold` algorithm will be generated.

## `CHECK_PANICS`

When enabled, Prusti will check for an absence of `panic!`s.

## `CONTRACTS_LIB`

Path to `libprusti_contracts*.rlib`.

## `DELETE_BASIC_BLOCKS`

The given basic blocks will be replaced with `assume false`.

## `DISABLE_NAME_MANGLING`

When enabled, Viper name mangling will be disabled.

**Note:** This is very likely to result in invalid programs being generated because of name collisions.

## `DUMP_BORROWCK_INFO`

When enabled, borrow checking info will be output.

## `DUMP_DEBUG_INFO`

When enabled, debug files will be created.

## `DUMP_PATH_CTXT_IN_DEBUG_INFO`

When enabled, branch context state will be output in debug files.

## `DUMP_REBORROWING_DAG_IN_DEBUG_INFO`

When enabled, reborrowing DAGs will be output in debug files.

## `DUMP_VIPER_PROGRAM`

When enabled, the encoded Viper program will be output.

## `ENABLE_VERIFY_ONLY_BASIC_BLOCK_PATH`

When enabled, only the path given in [`VERIFY_ONLY_BASIC_BLOCK_PATH`](#verify_only_basic_block_path) will be verified.

**Note:** This flag is only for debugging Prusti.

## `ENABLE_WHITELIST`

When enabled, the verification whitelist (specified using [`WHITELIST`](#whitelist)) will be used.

## `ENCODE_UNSIGNED_NUM_CONSTRAINT`

When enabled, non-negativity of unsigned integers will be encoded and checked.

## `ERROR_ON_PARTIALLY_SUPPORTED`

When enabled, any feature not supported by Prusti will trigger an error during verification.

This flag takes priority over [`SKIP_UNSUPPORTED_FEATURES`](#skip_unsupported_features).

## `EXTRA_JVM_ARGS`

Additional arguments to pass to the JVM when launching a verifier backend.

## `EXTRA_VERIFIER_ARGS`

Additional arguments to pass to the verifier backend.

## `FOLDUNFOLD_STATE_FILTER`

Filter for `fold`/`unfold` nodes when debug info is dumped.

## `FULL_COMPILATION`

When enabled, compilation will continue and a binary will be generated after Prusti terminates.

## `JSON_COMMUNICATION`

When enabled, communication with the server will be encoded as JSON instead of bincode.

## `LOG`

Log level and filters. See [`env_logger` documentation](https://docs.rs/env_logger/0.7.1/env_logger/index.html#enabling-logging).

## `LOG_DIR`

Path to directory in which log files and dumped output will be stored.

## `LOG_STYLE`

Log style. See [`env_logger` documentation](https://docs.rs/env_logger/0.7.1/env_logger/index.html#disabling-colors).

## `NO_VERIFY`

When enabled, verification is skipped altogether.

## `NUM_PARENTS_FOR_DUMPS`

Number of parent folders used to disambiguate Viper dumps (and other debug files).

## `QUIET`

When enabled, user messages are not printed. Otherwise, `message` outputs into `stderr`.

## `REPORT_SUPPORT_STATUS`

(deprecated)

## `SERVER_ADDRESS`

When set to an address and port (e.g. `"127.0.0.1:2468"`), Prusti will connect to the given server and use it for its verification backend.

When set to `"MOCK"`, the server is run off-thread, effectively mocking connecting to a server without having to start it up separately.

## `SERVER_MAX_CONCURRENCY`

The maximum amount of verification requests the server will work on concurrently. If not set, defaults to the number of (logical) cores on the system.

## `SERVER_MAX_STORED_VERIFIERS`

The maximum amount of instantiated Viper verifiers the server will keep around for reuse. If not set, defaults to `SERVER_MAX_CONCURRENT_VERIFICATION_OPERATIONS`. It also doesn't make much sense to set this option to less than that, since then the server will likely have to keep creating new verifiers, reducing the performance gained from reuse.

**Note:** This does _not_ limit how many verification requests the server handles concurrently, only the size of what is essentially its verifier cache.

## `SIMPLIFY_ENCODING`

When enabled, the encoded program is simplified before it is passed to the Viper backend.

## `SKIP_UNSUPPORTED_FEATURES`

When enabled, features not supported by Prusti will be reported as warnings rather than errors.

[`ERROR_ON_PARTIALLY_SUPPORTED`](#error_on_partially_supported) takes priority over this flag.

## `USE_MORE_COMPLETE_EXHALE`

When enabled, a more complete `exhale` version is used in the verifier. See [`consolidate`](https://github.com/viperproject/silicon/blob/f48de7f6e2d90d9020812869c713a5d3e2035995/src/main/scala/rules/StateConsolidator.scala#L29-L46). Equivalent to the verifier command-line argument `--enableMoreCompleteExhale`.

## `VERIFY_ONLY_BASIC_BLOCK_PATH`

Verify only the single execution path goes through the given basic blocks. All basic blocks not on this execution path are replaced with `assume false`. Must be enabled using the [`ENABLE_VERIFY_ONLY_BASIC_BLOCK_PATH`](#enable_verify_only_basic_block_path) flag.

**Note:** This option is only for debugging Prusti.

## `VERIFY_ONLY_PREAMBLE`

When enabled, only the preamble will be verified: domains, functions, and predicates.

**Note:** With this flag enabled, no methods are verified!

## `VIPER_BACKEND`

Verification backend to use. Possible values:

 - `Carbon` - verification-condition-generation-based backend [Carbon](https://github.com/viperproject/carbon).
 - `Silicon` - symbolic-execution-based backend [Silicon](https://github.com/viperproject/silicon/).

## `WHITELIST`

Whitelist of procedure names that should be verified. Must be enabled using the [`ENABLE_WHITELIST`](#enable_whitelist) flag.
