# List of Configuration Flags

| Name | Rust type | Default value |
| --- | --- | --- |
| [`ALLOW_UNREACHABLE_UNSUPPORTED_CODE`](#allow_unreachable_unsupported_code) | `bool` | `false` |
| [`ASSERT_TIMEOUT`](#assert_timeout) | `u64` | `10_000` |
| [`BE_RUSTC`](#be_rustc) | `bool` | `false` |
| [`BOOGIE_PATH`](#boogie_path) | `Option<String>` | `env::var("BOOGIE_EXE")` |
| [`CACHE_PATH`](#cache_path) | `String` | `""` |
| [`CHECK_FOLDUNFOLD_STATE`](#check_foldunfold_state) | `bool` | `false` |
| [`CHECK_OVERFLOWS`](#check_overflows) | `bool` | `true` |
| [`CHECK_PANICS`](#check_panics) | `bool` | `true` |
| [`CHECK_TIMEOUT`](#check_timeout) | `Option<u32>` | `None` |
| [`CONTRACTS_LIB`](#contracts_lib) | `String` | `""` |
| [`COUNTEREXAMPLE`](#counterexample) | `bool` | `false` |
| [`DELETE_BASIC_BLOCKS`](#delete_basic_blocks) | `Vec<String>` | `vec![]` |
| [`DISABLE_NAME_MANGLING`](#disable_name_mangling) | `bool` | `false` |
| [`DUMP_BORROWCK_INFO`](#dump_borrowck_info) | `bool` | `false` |
| [`DUMP_DEBUG_INFO`](#dump_debug_info) | `bool` | `false` |
| [`DUMP_DEBUG_INFO_DURING_FOLD`](#dump_debug_info_during_fold) | `bool` | `false` |
| [`DUMP_PATH_CTXT_IN_DEBUG_INFO`](#dump_path_ctxt_in_debug_info) | `bool` | `false` |
| [`DUMP_REBORROWING_DAG_IN_DEBUG_INFO`](#dump_reborrowing_dag_in_debug_info) | `bool` | `false` |
| [`DUMP_VIPER_PROGRAM`](#dump_viper_program) | `bool` | `false` |
| [`ENABLE_CACHE`](#enable_cache) | `bool` | `true` |
| [`ENABLE_GHOST_CONSTRAINTS`](#enable_ghost_constraints) | `bool` | `false` |
| [`ENABLE_PURIFICATION_OPTIMIZATION`](#enable_purification_optimization) | `bool` | `false` |
| [`ENABLE_TYPE_INVARIANTS`](#enable_type_invariants) | `bool` | `false` |
| [`ENABLE_VERIFY_ONLY_BASIC_BLOCK_PATH`](#enable_verify_only_basic_block_path) | `bool` | `false` |
| [`ENCODE_BITVECTORS`](#encode_bitvectors) | `bool` | `false` |
| [`ENCODE_UNSIGNED_NUM_CONSTRAINT`](#encode_unsigned_num_constraint) | `bool` | `false` |
| [`EXTRA_JVM_ARGS`](#extra_jvm_args) | `Vec<String>` | `vec![]` |
| [`EXTRA_VERIFIER_ARGS`](#extra_verifier_args) | `Vec<String>` | `vec![]` |
| [`FOLDUNFOLD_STATE_FILTER`](#foldunfold_state_filter) | `String` | `""` |
| [`FULL_COMPILATION`](#full_compilation) | `bool` | `false` |
| [`HIDE_UUIDS`](#hide_uuids) | `bool` | `false` |
| [`IGNORE_REGIONS`](#ignore_regions) | `bool` | `false` |
| [`INTERNAL_ERRORS_AS_WARNINGS`](#internal_errors_as_warnings) | `bool` | `false` |
| [`INTERN_NAMES`](#intern_names) | `bool` | `true` |
| [`JAVA_HOME`](#java_home) | `Option<String>` | `None` |
| [`JSON_COMMUNICATION`](#json_communication) | `bool` | `false` |
| [`LOG`](#log) | `Option<String>` | `None` |
| [`LOG_DIR`](#log_dir) | `String` | `"log"` |
| [`LOG_STYLE`](#log_style) | `String` | `"auto"` |
| [`LOG_SMT_WRAPPER_INTERACTION`](#log_smt_wrapper_interaction) | `bool` | `false` |
| [`MAX_LOG_FILE_NAME_LENGTH`](#max_log_file_name_length) | `usize` | `60` |
| [`NO_VERIFY`](#no_verify) | `bool` | `false` |
| [`NO_VERIFY_DEPS`](#no_verify_deps) | `bool` | `false` |
| [`OPTIMIZATIONS`](#optimizations) | `Vec<String>` | "all" |
| [`PRESERVE_SMT_TRACE_FILES`](#preserve_smt_trace_files) | `bool` | `false` |
| [`PRINT_COLLECTED_VERIFICATION_ITEMS`](#print_collected_verification_items) | `bool` | `false` |
| [`PRINT_DESUGARED_SPECS`](#print_desugared_specs) | `bool` | `false` |
| [`PRINT_HASH`](#print_hash) | `bool` | `false` |
| [`PRINT_TYPECKD_SPECS`](#print_typeckd_specs) | `bool` | `false` | `bool` | `false` |
| [`QUIET`](#quiet) | `bool` | `false` |
| [`SERVER_ADDRESS`](#server_address) | `Option<String>` | `None` |
| [`SERVER_MAX_CONCURRENCY`](#server_max_concurrency) | `Option<usize>` | `None` |
| [`SERVER_MAX_STORED_VERIFIERS`](#server_max_stored_verifiers) | `Option<usize>` | `None` |
| [`SIMPLIFY_ENCODING`](#simplify_encoding) | `bool` | `true` |
| [`SKIP_UNSUPPORTED_FEATURES`](#skip_unsupported_features) | `bool` | `false` |
| [`SMT_QUANTIFIER_INSTANTIATIONS_BOUND_GLOBAL`](#smt_quantifier_instantiations_bound_global) | `Option<u64>` | `None` |
| [`SMT_QUANTIFIER_INSTANTIATIONS_BOUND_GLOBAL_KIND`](#smt_quantifier_instantiations_bound_global_kind) | `Option<u64>` | `None` |
| [`SMT_QUANTIFIER_INSTANTIATIONS_BOUND_TRACE`](#smt_quantifier_instantiations_bound_trace) | `Option<u64>` | `None` |
| [`SMT_QUANTIFIER_INSTANTIATIONS_BOUND_TRACE_KIND`](#smt_quantifier_instantiations_bound_trace_kind) | `Option<u64>` | `None` |
| [`SMT_QUANTIFIER_INSTANTIATIONS_IGNORE_BUILTIN`](#smt_quantifier_instantiations_ignore_builtin) | `bool` | `true` |
| [`SMT_QI_EAGER_THRESHOLD`](#smt_qi_eager_threshold) | `u64` | `1000` |
| [`SMT_SOLVER_PATH`](#smt_solver_path) | `Option<String>` | `env::var("Z3_EXE")` |
| [`SMT_SOLVER_WRAPPER_PATH`](#smt_solver_wrapper_path) | `Option<String>` | `None` |
| [`SMT_UNIQUE_TRIGGERS_BOUND`](#smt_unique_triggers_bound) | `Option<u64>` | `None` |
| [`SMT_UNIQUE_TRIGGERS_BOUND_TOTAL`](#smt_unique_triggers_bound_total) | `Option<u64>` | `None` |
| [`UNSAFE_CORE_PROOF`](#unsafe_core_proof) | `bool` | `false` |
| [`USE_MORE_COMPLETE_EXHALE`](#use_more_complete_exhale) | `bool` | `true` |
| [`USE_SMT_WRAPPER`](#use_smt_wrapper) | `bool` | `false` |
| [`VERIFICATION_DEADLINE`](#verification_deadline) | `Option<u64>` | `None` |
| [`VERIFY_ONLY_BASIC_BLOCK_PATH`](#verify_only_basic_block_path) | `Vec<String>` | `vec![]` |
| [`VERIFY_ONLY_PREAMBLE`](#verify_only_preamble) | `bool` | `false` |
| [`VIPER_BACKEND`](#viper_backend) | `String` | `"Silicon"` |
| [`VIPER_HOME`](#viper_home) | `Option<String>` | `None` |
| [`WRITE_SMT_STATISTICS`](#write_smt_statistics) | `bool` | `false` |

## `ALLOW_UNREACHABLE_UNSUPPORTED_CODE`

When enabled, unsupported code is encoded as `assert false`. This way error messages are reported only for unsupported code that is actually reachable.

## `ASSERT_TIMEOUT`

Maximum time (in milliseconds) for the verifier to spend on a single assertion. Set to `0` to disable timeout. Maps to the verifier command-line argument `--assertTimeout`.

## `BE_RUSTC`

When enabled, Prusti will behave like `rustc`.

## `BOOGIE_PATH`

A path to Boogie.

**Note:** `prusti-rustc` sets this option.

## `CACHE_PATH`

Path to a cache file, where verification cache will be loaded from and saved to. The default empty string disables saving any cache to disk. A path to a file which does not yet exist will result in using an empty cache, but then creating and saving to that location on exit.

## `CHECK_FOLDUNFOLD_STATE`

When enabled, additional, *slow*, checks for the `fold`/`unfold` algorithm will be generated.

## `CHECK_OVERFLOWS`

When enabled, binary operations and numeric casts will be checked for overflows. See [integer type encoding](../encoding/types-heap.md#i-u-char).

## `CHECK_PANICS`

When enabled, Prusti will check for an absence of `panic!`s.

## `CHECK_TIMEOUT`

Maximum time (in milliseconds) for the verifier to spend on checks.
Set to None uses the verifier's default value. Maps to the verifier command-line
argument `--checkTimeout`.
For more information see [here]( https://github.com/viperproject/silicon/blob/4c70514379f89e7ec6f96588290ade32518f0527/src/main/scala/Config.scala#L203).


## `CONTRACTS_LIB`

Path to `libprusti_contracts*.rlib`.

## `COUNTEREXAMPLE`

When enabled, Prusti will try to find and print a counterexample for any failed assertion or specification.

## `DELETE_BASIC_BLOCKS`

The given basic blocks will be replaced with `assume false`.

## `DISABLE_NAME_MANGLING`

When enabled, Viper name mangling will be disabled.

**Note:** This is very likely to result in invalid programs being generated because of name collisions.

## `DUMP_BORROWCK_INFO`

When enabled, borrow checking info will be output.

## `DUMP_DEBUG_INFO`

When enabled, debug files will be created.

## `DUMP_DEBUG_INFO_DURING_FOLD`

When enabled, the state of the fold-unfold algorithm after each step will be dumped to a file.

## `DUMP_PATH_CTXT_IN_DEBUG_INFO`

When enabled, branch context state will be output in debug files.

## `DUMP_REBORROWING_DAG_IN_DEBUG_INFO`

When enabled, reborrowing DAGs will be output in debug files.

## `DUMP_VIPER_PROGRAM`

When enabled, the encoded Viper program will be output.

## `ENABLE_CACHE`

When enabled, verification requests (to verify individual `fn`s) are cached to improve future verification. By default the cache is only saved in memory (of the `prusti-server` if enabled). For long-running verification projects use [`CACHE_PATH`](#cache_path) to save to disk.

## `ENABLE_GHOST_CONSTRAINTS`

When enabled, ghost constraints can be used in Prusti specifications.

Ghost constraints allow for specifications which are only active if a certain "constraint" (i.e. a trait bound
on a generic type parameter) is satisfied.

**This is an experimental feature**, because it is currently possible to introduce unsound verification behavior.

## `ENABLE_PURIFICATION_OPTIMIZATION`

When enabled, impure methods are optimized using the purification optimization, which tries to convert heap operations to pure (snapshot-based) operations.

**Note:** This option is highly experimental.

## `ENABLE_TYPE_INVARIANTS`

When enabled, type invariants can be declared on types using the `#[invariant(...)]` attribute.

## `ENABLE_VERIFY_ONLY_BASIC_BLOCK_PATH`

When enabled, only the path given in [`VERIFY_ONLY_BASIC_BLOCK_PATH`](#verify_only_basic_block_path) will be verified.

**Note:** This flag is only for debugging Prusti.

## `ENCODE_BITVECTORS`

When enabled, bitwise integer operations are encoded using bitvectors.

**Note:** This option is highly experimental.

## `ENCODE_UNSIGNED_NUM_CONSTRAINT`

When enabled, non-negativity of unsigned integers will be encoded and checked.

## `EXTRA_JVM_ARGS`

Additional arguments to pass to the JVM when launching a verifier backend.

## `EXTRA_VERIFIER_ARGS`

Additional arguments to pass to the verifier backend.

## `FOLDUNFOLD_STATE_FILTER`

Filter for `fold`/`unfold` nodes when debug info is dumped.

## `FULL_COMPILATION`

When enabled, compilation will continue and a binary will be generated after Prusti terminates.

## `HIDE_UUIDS`

When enabled, UUIDs of expressions and specifications printed with [`PRINT_TYPECKD_SPECS`](#print_typeckd_specs) are hidden.

## `IGNORE_REGIONS`

When enabled, debug files dumped by `rustc` will not contain lifetime regions.

## `INTERNAL_ERRORS_AS_WARNINGS`

When enabled, internal errors are presented as warnings.

**Note**: This should only be used for debugging, as enabling this setting could
hide actual verification errors.

## `INTERN_NAMES`

When enabled, Viper identifiers are interned to shorten them when possible.

## `JAVA_HOME`

The path the directory containing Java.

**Note:** `prusti-rustc` sets this option.

## `JSON_COMMUNICATION`

When enabled, communication with the server will be encoded as JSON instead of the default bincode.

## `LOG`

Log level and filters. See [`env_logger` documentation](https://docs.rs/env_logger/0.7.1/env_logger/index.html#enabling-logging).

## `LOG_DIR`

Path to directory in which log files and dumped output will be stored.

## `LOG_STYLE`

Log style. See [`env_logger` documentation](https://docs.rs/env_logger/0.7.1/env_logger/index.html#disabling-colors).

## `LOG_SMT_WRAPPER_INTERACTION`

When enabled, logs all SMT wrapper interaction to a file.

**Note:** Requires `USE_SMT_WRAPPER` to be `true`.

## `MAX_LOG_FILE_NAME_LENGTH`

Maximum allowed length of a log file name. If this is exceeded, the file name is truncated.

## `NO_VERIFY`

When enabled, verification is skipped altogether.

## `NO_VERIFY_DEPS`

When enabled, verification is skipped for dependencies.

## `ONLY_MEMORY_SAFETY`

When enabled, only the core proof is verified.

**Note:** This should be used only when `UNSAFE_CORE_PROOF` is enabled.

## `OPTIMIZATIONS`

Comma-separated list of optimizations to enable, or `"all"` to enable all. Possible values in the list are:

- `"inline_constant_functions"`
- `"delete_unused_predicates"`
- `"optimize_folding"`
- `"remove_empty_if"`
- `"purify_vars"`
- `"fix_quantifiers"`
- `"fix_unfoldings"`
- `"remove_unused_vars"`
- `"remove_trivial_assertions"`
- `"clean_cfg"`

## `PRESERVE_SMT_TRACE_FILES`

When enabled, does not delete Z3 trace files.

**Note:** Requires `USE_SMT_WRAPPER` to be `true`.

## `PRINT_COLLECTED_VERIFICATION_ITEMS`

When enabled, prints the items collected for verification.

## `PRINT_DESUGARED_SPECS`

When enabled, prints the AST with desugared specifications.

## `PRINT_HASH`

When enabled, prints the hash of a verification request (the hash is used for caching). This is a debugging option which does not perform verification &mdash; it is similar to [`NO_VERIFY`](#no_verify), except that this flag stops the verification process at a later stage.

## `PRINT_TYPECKD_SPECS`

When enabled, prints the type-checked specifications.

## `QUIET`

When enabled, user messages are not printed. Otherwise, messages output into `stderr`.

## `SERVER_ADDRESS`

When set to an address and port (e.g. `"127.0.0.1:2468"`), Prusti will connect to the given server and use it for its verification backend.

When set to `"MOCK"`, the server is run off-thread, effectively mocking connecting to a server without having to start it up separately.

## `SERVER_MAX_CONCURRENCY`

Maximum amount of verification requests the server will work on concurrently. If not set, defaults to the number of (logical) cores on the system.

## `SERVER_MAX_STORED_VERIFIERS`

Maximum amount of instantiated Viper verifiers the server will keep around for reuse. If not set, defaults to `SERVER_MAX_CONCURRENT_VERIFICATION_OPERATIONS`. It also doesn't make much sense to set this option to less than that, since then the server will likely have to keep creating new verifiers, reducing the performance gained from reuse.

**Note:** This does _not_ limit how many verification requests the server handles concurrently, only the size of what is essentially its verifier cache.

## `SIMPLIFY_ENCODING`

When enabled, the encoded program is simplified before it is passed to the Viper backend.

## `SKIP_UNSUPPORTED_FEATURES`

When enabled, features not supported by Prusti will be reported as warnings rather than errors.

## `SMT_QUANTIFIER_INSTANTIATIONS_BOUND_GLOBAL`

If not `None`, checks that the number of global quantifier instantiations reported by the SMT wrapper is smaller than the specified bound.

**Note:** Requires `USE_SMT_WRAPPER` to be `true`.

## `SMT_QUANTIFIER_INSTANTIATIONS_BOUND_GLOBAL_KIND`

If not `None`, checks that the number of global quantifier instantiations for each quantifier reported by the SMT wrapper is smaller than the specified bound.

**Note:** Requires `USE_SMT_WRAPPER` to be `true`.

## `SMT_QUANTIFIER_INSTANTIATIONS_BOUND_TRACE`

If not `None`, checks that the number of quantifier instantiations in each trace reported by the SMT wrapper is smaller than the specified bound.

**Note:** Requires `USE_SMT_WRAPPER` to be `true`.

## `SMT_QUANTIFIER_INSTANTIATIONS_BOUND_TRACE_KIND`

If not `None`, checks that the number of quantifier instantiations in each trace for each quantifier reported by the SMT wrapper is smaller than the specified bound.

**Note:** Requires `USE_SMT_WRAPPER` to be `true`.

## `SMT_QUANTIFIER_INSTANTIATIONS_IGNORE_BUILTIN`

When enabled, ignores the built-in quantifiers in SMT quantifier instantiation bounds checking.

## `SMT_QI_EAGER_THRESHOLD`

A threshold controlling how many times Z3 should instantiate a single quantifier. This option controls a tradeoff between performance and completeness:

* Setting it to a too small value, may lead to spurious verification errors and unstable verification.
+ Setting it to a too large value, may significantly impact performance.

## `SMT_SOLVER_PATH`

Path to Z3.

**Note:** `prusti-rustc` sets this option.

## `SMT_SOLVER_WRAPPER_PATH`

A path to `prusti-smt-solver`.

**Note:** `prusti-rustc` sets this option.

## `SMT_UNIQUE_TRIGGERS_BOUND`

If not `None`, checks that the number of unique triggers used for each quantifier reported by the SMT wrapper is smaller than the specified bound.

**Note:** Requires `USE_SMT_WRAPPER` to be `true`.

## `SMT_UNIQUE_TRIGGERS_BOUND_TOTAL`

If not `None`, checks that the total number of unique triggers reported by the SMT wrapper is smaller than the specified bound.

**Note:** Requires `USE_SMT_WRAPPER` to be `true`.

## `UNSAFE_CORE_PROOF`

When enabled, the new core proof is used, suitable for unsafe code

**Note:** This option is currently very incomplete.

## `USE_MORE_COMPLETE_EXHALE`

When enabled, a more complete `exhale` version is used in the verifier. See [`consolidate`](https://github.com/viperproject/silicon/blob/f48de7f6e2d90d9020812869c713a5d3e2035995/src/main/scala/rules/StateConsolidator.scala#L29-L46). Equivalent to the verifier command-line argument `--enableMoreCompleteExhale`.

## `USE_SMT_WRAPPER`

Whether to use the SMT solver wrapper. Enabling this is required to be able to use quantifier instantiation bounds checking.

This flag is intended to be used in tests only.

## `VERIFICATION_DEADLINE`

Deadline (in seconds) within which Prusti should encode and verify the program.

Prusti panics if it fails to meet this deadline. This flag is intended to be used for tests that aim to catch performance regressions.

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

## `VIPER_HOME`

The path the directory containing the Viper JARs.

**Note:** `prusti-rustc` sets this option.

## `WRITE_SMT_STATISTICS`

When enabled, dumps the statistics collected by the SMT wrapper into files next to the Z3 trace files.

**Note:** Requires `USE_SMT_WRAPPER` to be `true`.
