// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![allow(deprecated)]

pub mod commandline;

use self::commandline::CommandLine;
use crate::launch::{find_viper_home, get_current_executable_dir};
use ::config::{Config, Environment, File};
use log::warn;
use rustc_hash::FxHashSet;
use serde::Deserialize;
use std::{env, path::PathBuf, sync::RwLock};

#[derive(Debug, PartialEq, Eq)]
pub struct Optimizations {
    pub inline_constant_functions: bool,
    pub delete_unused_predicates: bool,
    pub optimize_folding: bool,
    pub remove_empty_if: bool,
    pub purify_vars: bool,
    pub fix_quantifiers: bool,
    pub fix_unfoldings: bool,
    pub remove_unused_vars: bool,
    pub remove_trivial_assertions: bool,
    pub clean_cfg: bool,
}

impl Optimizations {
    fn all_disabled() -> Self {
        Optimizations {
            inline_constant_functions: false,
            delete_unused_predicates: false,
            optimize_folding: false,
            remove_empty_if: false,
            purify_vars: false,
            fix_quantifiers: false,
            fix_unfoldings: false,
            remove_unused_vars: false,
            remove_trivial_assertions: false,
            clean_cfg: false,
        }
    }

    fn all_enabled() -> Self {
        Optimizations {
            inline_constant_functions: true,
            delete_unused_predicates: true,
            optimize_folding: true,
            remove_empty_if: true,
            purify_vars: true,
            fix_quantifiers: true,
            // Disabled because https://github.com/viperproject/prusti-dev/issues/892 has been fixed
            fix_unfoldings: false,
            remove_unused_vars: true,
            remove_trivial_assertions: true,
            clean_cfg: true,
        }
    }
}

lazy_static::lazy_static! {
    // Is this RwLock<..> necessary?
    static ref SETTINGS: RwLock<Config> = RwLock::new({
        let mut settings = Config::default();

        // 0. Default values
        settings.set_default("be_rustc", false).unwrap();
        settings.set_default("viper_backend", "Silicon").unwrap();
        settings.set_default::<Option<String>>("smt_solver_path", env::var("Z3_EXE").ok()).unwrap();
        settings.set_default::<Option<String>>("smt_solver_wrapper_path", None).unwrap();
        settings.set_default::<Option<String>>("boogie_path", env::var("BOOGIE_EXE").ok()).unwrap();
        settings.set_default::<Option<String>>("viper_home", None).unwrap();
        settings.set_default::<Option<String>>("java_home", None).unwrap();

        settings.set_default::<Option<u32>>("check_timeout", None).unwrap();
        settings.set_default("check_foldunfold_state", false).unwrap();
        settings.set_default("check_overflows", true).unwrap();
        settings.set_default("check_panics", true).unwrap();
        settings.set_default("encode_unsigned_num_constraint", true).unwrap();
        settings.set_default("encode_bitvectors", false).unwrap();
        settings.set_default("simplify_encoding", true).unwrap();
        settings.set_default("log", "").unwrap();
        settings.set_default("log_style", "auto").unwrap();
        settings.set_default("log_dir", "log").unwrap();
        settings.set_default("log_tracing", true).unwrap();
        settings.set_default("cache_path", "").unwrap();
        settings.set_default("dump_debug_info", false).unwrap();
        settings.set_default("dump_debug_info_during_fold", false).unwrap();
        settings.set_default("dump_nll_facts", false).unwrap();
        settings.set_default("ignore_regions", false).unwrap();
        settings.set_default("max_log_file_name_length", 60).unwrap();
        settings.set_default("dump_path_ctxt_in_debug_info", false).unwrap();
        settings.set_default("dump_reborrowing_dag_in_debug_info", false).unwrap();
        settings.set_default("dump_borrowck_info", false).unwrap();
        settings.set_default("dump_viper_program", false).unwrap();
        settings.set_default("foldunfold_state_filter", "").unwrap();
        settings.set_default::<Vec<String>>("extra_jvm_args", vec![]).unwrap();
        settings.set_default::<Vec<String>>("extra_verifier_args", vec![]).unwrap();
        settings.set_default("quiet", false).unwrap();
        settings.set_default("assert_timeout", 10_000).unwrap();
        settings.set_default("smt_qi_eager_threshold", 1000).unwrap();
        settings.set_default("smt_use_nonlinear_arithmetic_solver", false).unwrap();
        settings.set_default("use_more_complete_exhale", false).unwrap();
        settings.set_default("use_carbon_qps", true).unwrap();
        settings.set_default("use_z3_api", false).unwrap();
        settings.set_default("skip_unsupported_features", false).unwrap();
        settings.set_default("internal_errors_as_warnings", false).unwrap();
        settings.set_default("allow_unreachable_unsupported_code", false).unwrap();
        settings.set_default("no_verify", false).unwrap();
        settings.set_default("no_verify_deps", false).unwrap();
        settings.set_default("opt_in_verification", false).unwrap();
        settings.set_default("full_compilation", false).unwrap();
        settings.set_default("json_communication", false).unwrap();
        settings.set_default("optimizations", "all").unwrap();
        settings.set_default("intern_names", true).unwrap();
        settings.set_default("create_missing_storage_live", false).unwrap();
        settings.set_default("enable_purification_optimization", false).unwrap();
        // settings.set_default("enable_manual_axiomatization", false).unwrap();
        settings.set_default("unsafe_core_proof", false).unwrap();
        settings.set_default("custom_heap_encoding", false).unwrap();
        settings.set_default("trace_with_symbolic_execution", false).unwrap();
        settings.set_default("trace_with_symbolic_execution_new", true).unwrap();
        settings.set_default("purify_with_symbolic_execution", false).unwrap();
        settings.set_default("symbolic_execution_single_method", true).unwrap();
        settings.set_default("symbolic_execution_leak_check", true).unwrap();
        settings.set_default("panic_on_failed_exhale", false).unwrap();
        settings.set_default("panic_on_failed_exhale_materialization", true).unwrap();
        settings.set_default("materialize_on_failed_exhale", false).unwrap();
        settings.set_default("ignore_whether_exhale_is_unconditional", false).unwrap();
        settings.set_default("error_non_linear_arithmetic_simp", true).unwrap();
        settings.set_default("expand_quantifiers", false).unwrap();
        settings.set_default("report_symbolic_execution_failures", false).unwrap();
        settings.set_default("report_symbolic_execution_purification", false).unwrap();
        settings.set_default("verify_core_proof", true).unwrap();
        settings.set_default("verify_specifications", true).unwrap();
        settings.set_default("verify_types", false).unwrap();
        settings.set_default("verify_specifications_with_core_proof", true).unwrap();
        settings.set_default("verify_specifications_backend", "Silicon").unwrap();
        settings.set_default("use_eval_axioms", true).unwrap();
        settings.set_default("inline_caller_for", false).unwrap();
        settings.set_default("use_snapshot_parameters_in_predicates", false).unwrap();
        settings.set_default("check_no_drops", false).unwrap();
        settings.set_default("enable_type_invariants", false).unwrap();
        settings.set_default("use_new_encoder", true).unwrap();
        settings.set_default::<Option<u8>>("number_of_parallel_verifiers", None).unwrap();
        settings.set_default::<Option<String>>("min_prusti_version", None).unwrap();

        settings.set_default("print_desugared_specs", false).unwrap();
        settings.set_default("print_typeckd_specs", false).unwrap();
        settings.set_default("print_collected_verification_items", false).unwrap();
        settings.set_default("hide_uuids", false).unwrap();
        settings.set_default("counterexample", false).unwrap();
        settings.set_default("print_counterexample_if_model_is_present", false).unwrap();
        settings.set_default::<Option<String>>("save_failing_trace_to_file", None).unwrap();
        settings.set_default::<Option<String>>("execute_only_failing_trace", None).unwrap();
        settings.set_default::<Option<String>>("dump_fold_unfold_state_of_blocks", None).unwrap();
        settings.set_default("print_hash", false).unwrap();
        settings.set_default("enable_cache", true).unwrap();

        settings.set_default("cargo_path", "cargo").unwrap();
        settings.set_default("cargo_command", "check").unwrap();

        // Flags for testing.
        settings.set_default::<Option<i64>>("verification_deadline", None).unwrap();
        settings.set_default("use_smt_wrapper", false).unwrap();
        settings.set_default("smt_qi_ignore_builtin", true).unwrap();
        settings.set_default::<Option<u64>>("smt_qi_bound_global", None).unwrap();
        settings.set_default::<Option<u64>>("smt_qi_bound_global_kind", None).unwrap();
        settings.set_default::<Option<u64>>("smt_qi_bound_trace", None).unwrap();
        settings.set_default::<Option<u64>>("smt_qi_bound_trace_kind", None).unwrap();
        settings.set_default::<Option<u64>>("smt_unique_triggers_bound", None).unwrap();
        settings.set_default::<Option<u64>>("smt_unique_triggers_bound_total", None).unwrap();

        // Flags for debugging performance.
        settings.set_default("preserve_smt_trace_files", false).unwrap();
        settings.set_default("write_smt_statistics", false).unwrap();
        settings.set_default("log_smt_wrapper_interaction", false).unwrap();

        // Flags for debugging Prusti that can change verification results.
        settings.set_default("disable_name_mangling", false).unwrap();
        settings.set_default("verify_only_preamble", false).unwrap();
        settings.set_default("enable_verify_only_basic_block_path", false).unwrap();
        settings.set_default::<Vec<String>>("verify_only_basic_block_path", vec![]).unwrap();
        settings.set_default::<Vec<String>>("delete_basic_blocks", vec![]).unwrap();

        // Get the list of all allowed flags.
        let mut allowed_keys = get_keys(&settings);
        allowed_keys.insert("server_max_stored_verifiers".to_string());
        allowed_keys.insert("server_max_concurrency".to_string());
        allowed_keys.insert("server_address".to_string());
        allowed_keys.insert("config".to_string());
        allowed_keys.insert("log".to_string());
        allowed_keys.insert("log_style".to_string());
        allowed_keys.insert("rustc_log_args".to_string());
        allowed_keys.insert("rustc_log_env".to_string());
        allowed_keys.insert("original_smt_solver_path".to_string());

        // TODO: reduce this to something more sensible:
        static MAX_CONFIG_LEN: usize = 40;
        debug_assert!(
            allowed_keys.iter().all(|key| key.len() <= MAX_CONFIG_LEN),
            "Hey Prusti dev, please reduce the length of these configs: {:?}. \
            Long configs are a pain to work with and list out in the guide.",
            allowed_keys.iter().filter(|key| key.len() > MAX_CONFIG_LEN).collect::<Vec<_>>()
        );

        // 1. Override with default env variables (e.g. `DEFAULT_PRUSTI_CACHE_PATH`, ...)
        settings.merge(
            Environment::with_prefix("DEFAULT_PRUSTI").ignore_empty(true)
        ).unwrap();
        check_keys(&settings, &allowed_keys, "default environment variables");

        // 2. Override with an optional "Prusti.toml" file in manifest dir
        let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
        let file = PathBuf::from(manifest_dir).join("Prusti.toml");
        settings.merge(File::from(file.as_path()).required(false)).unwrap();
        check_keys(&settings, &allowed_keys, &format!("{} file", file.to_string_lossy()));

        // 3. Override with env variables (`PRUSTI_VIPER_BACKEND`, ...)
        settings.merge(
            Environment::with_prefix("PRUSTI")
                .ignore_empty(true)
                .try_parsing(true)
                .with_list_parse_key("delete_basic_blocks")
                .with_list_parse_key("extra_jvm_args")
                .with_list_parse_key("extra_verifier_args")
                .with_list_parse_key("verify_only_basic_block_path")
                .list_separator(" ")
        ).unwrap();
        check_keys(&settings, &allowed_keys, "environment variables");

        // 4. Override with command-line arguments -P<arg>=<val>
        settings.merge(
            CommandLine::with_prefix("-P").ignore_invalid(true)
        ).unwrap();
        check_keys(&settings, &allowed_keys, "command line arguments");

        settings
    });
}

fn get_keys(settings: &Config) -> FxHashSet<String> {
    settings
        .cache
        .clone()
        .into_table()
        .unwrap()
        .into_keys()
        .collect()
}

fn check_keys(settings: &Config, allowed_keys: &FxHashSet<String>, source: &str) {
    for key in settings.cache.clone().into_table().unwrap().keys() {
        assert!(
            allowed_keys.contains(key),
            "{source} contains unknown configuration flag: “{key}”",
        );
    }
}

/// Return vector of arguments filtered out by prefix
pub fn get_filtered_args() -> Vec<String> {
    CommandLine::with_prefix("-P")
        .get_remaining_args()
        .collect::<Vec<String>>()
}

/// Generate a dump of the settings
pub fn dump() -> String {
    let settings = SETTINGS.read().unwrap();
    let map = config::Source::collect(&*settings).unwrap();
    let mut pairs: Vec<_> = map
        .iter()
        .map(|(key, value)| format!("{key}={value:#?}"))
        .collect();
    pairs.sort();
    pairs.join("\n\n")
}

fn read_optional_setting<T>(name: &'static str) -> Option<T>
where
    T: Deserialize<'static>,
{
    SETTINGS.read().unwrap().get(name).ok()
}

fn read_setting<T>(name: &'static str) -> T
where
    T: Deserialize<'static>,
{
    SETTINGS
        .read()
        .unwrap()
        .get(name)
        .unwrap_or_else(|e| panic!("Failed to read setting {name} due to {e}"))
}

fn write_setting<T: Into<config::Value>>(key: &'static str, value: T) {
    SETTINGS
        .write()
        .unwrap()
        .set(key, value)
        .unwrap_or_else(|e| panic!("Failed to write setting {key} due to {e}"));
}

// The following methods are all convenience wrappers for the actual call to
// `read_setting` (+ optionally some light sanitisation or processing). Please
// keep the documentation on each method in sync with `flags.md` in the dev
// guide!

/// When enabled, Prusti will behave like `rustc`.
pub fn be_rustc() -> bool {
    read_setting("be_rustc")
}

/// When enabled, additional, *slow*, checks for the `fold`/`unfold` algorithm
/// will be generated.
pub fn check_foldunfold_state() -> bool {
    read_setting("check_foldunfold_state")
}

/// Verification backend to use. Possible values:
///
/// - `Carbon` - verification-condition-generation-based backend
///   [Carbon](https://github.com/viperproject/carbon).
/// - `Silicon` - symbolic-execution-based backend
///   [Silicon](https://github.com/viperproject/silicon/).
pub fn viper_backend() -> String {
    read_setting::<String>("viper_backend")
        .to_lowercase()
        .trim()
        .to_string()
}

/// The path to the SMT solver to use. `prusti-rustc` is expected to set this
/// configuration flag to the correct path to Z3.
pub fn smt_solver_path() -> String {
    read_setting::<Option<String>>("smt_solver_path")
        .expect("please set the smt_solver_path configuration flag")
}

/// The path to the SMT solver wrapper. `prusti-rustc` is expected to set this
/// configuration flag to the correct path.
pub fn smt_solver_wrapper_path() -> String {
    read_setting::<Option<String>>("smt_solver_wrapper_path")
        .expect("please set the smt_solver_wrapper_path configuration flag")
}

/// The path to the Boogie executable. `prusti-rustc` is expected to set this
/// configuration flag to the correct path.
pub fn boogie_path() -> Option<String> {
    read_setting::<Option<String>>("boogie_path")
}

/// The path to the Viper JARs. `prusti-rustc` is expected to set this
/// configuration flag to the correct path.
pub fn viper_home() -> String {
    if let Some(path) = read_setting::<Option<String>>("viper_home") {
        path
    } else {
        // If we are running tests, the VIPER_HOME should be in a directory
        // relative to us.
        let current_executable_dir = get_current_executable_dir();
        if let Some(path) = find_viper_home(&current_executable_dir) {
            path.to_str().unwrap().to_owned()
        } else {
            panic!("Failed to detect Vipe home, please set viper_home configuration flag")
        }
    }
}

/// The path to the Viper JARs. `prusti-rustc` is expected to set this
/// configuration flag to the correct path.
pub fn java_home() -> String {
    read_setting::<Option<String>>("java_home")
        .expect("please set the java_home configuration flag")
}

/// When enabled, Prusti will check for an absence of `panic!`s.
pub fn check_panics() -> bool {
    read_setting("check_panics")
}

/// When enabled, the encoded program is simplified before it is passed to
/// the Viper backend.
pub fn simplify_encoding() -> bool {
    read_setting("simplify_encoding")
}

/// When enabled, debug files will be created.
pub fn dump_debug_info() -> bool {
    read_setting("dump_debug_info")
}

/// When enabled, the state of the fold-unfold algorithm after each step will
/// be dumped to a file.
pub fn dump_debug_info_during_fold() -> bool {
    read_setting("dump_debug_info_during_fold")
}

/// When enabled, dumps Polonius nll-facts in the log directory.
pub fn dump_nll_facts() -> bool {
    read_setting("dump_nll_facts")
}

/// When enabled, debug files dumped by `rustc` will not contain lifetime
/// regions.
pub fn ignore_regions() -> bool {
    read_setting("ignore_regions")
}

/// Maximum allowed length of a log file name. If this is exceeded, the file
/// name is truncated.
pub fn max_log_file_name_length() -> usize {
    read_setting("max_log_file_name_length")
}

/// When enabled, branch context state will be output in debug files.
pub fn dump_path_ctxt_in_debug_info() -> bool {
    read_setting("dump_path_ctxt_in_debug_info")
}

/// When enabled, reborrowing DAGs will be output in debug files.
pub fn dump_reborrowing_dag_in_debug_info() -> bool {
    read_setting("dump_reborrowing_dag_in_debug_info")
}

/// When enabled, borrow checking info will be output.
pub fn dump_borrowck_info() -> bool {
    read_setting("dump_borrowck_info")
}

/// When enabled, the encoded Viper program will be output.
pub fn dump_viper_program() -> bool {
    read_setting("dump_viper_program")
}

/// Filter for `fold`/`unfold` nodes when debug info is dumped.
pub fn foldunfold_state_filter() -> String {
    read_setting("foldunfold_state_filter")
}

/// Set the log level of `env_logger`.
pub fn log() -> String {
    read_setting("log")
}

/// Set the log style when logging is enabled by `log`.
pub fn log_style() -> String {
    read_setting("log_style")
}

/// Path to directory in which log files and dumped output will be stored.
pub fn log_dir() -> PathBuf {
    PathBuf::from(read_setting::<String>("log_dir"))
}

/// When enabled, trace using tracing_chrome crate.
pub fn log_tracing() -> bool {
    read_setting("log_tracing")
}

/// Path to a cache file, where verification cache will be loaded from and
/// saved to. The default empty string disables saving any cache to disk.
/// A path to a file which does not yet exist will result in using an empty
/// cache, but then creating and saving to that location on exit.
pub fn cache_path() -> PathBuf {
    PathBuf::from(read_setting::<String>("cache_path"))
}

/// When enabled, binary operations and numeric casts will be checked for
/// overflows.
pub fn check_overflows() -> bool {
    read_setting("check_overflows")
}

/// When enabled, non-negativity of unsigned integers will be encoded and
/// checked.
pub fn encode_unsigned_num_constraint() -> bool {
    read_setting("encode_unsigned_num_constraint")
}

/// When enabled, bitwise integer operations are encoded using bitvectors.
///
/// **Note:** this option is highly experimental.
pub fn encode_bitvectors() -> bool {
    read_setting("encode_bitvectors")
}

/// Additional arguments to pass to the JVM when launching a verifier backend.
pub fn extra_jvm_args() -> Vec<String> {
    read_setting("extra_jvm_args")
}

/// Additional arguments to pass to the verifier backend.
pub fn extra_verifier_args() -> Vec<String> {
    read_setting("extra_verifier_args")
}

/// When enabled, user messages are not printed. Otherwise, message output
/// into `stderr`.
pub fn quiet() -> bool {
    read_setting("quiet")
}

/// Maximum time (in milliseconds) for the verifier to spend on a single
/// assertion. Set to `0` to disable timeout. Maps to the verifier command-line
/// argument `--assertTimeout`.
pub fn assert_timeout() -> u64 {
    read_setting("assert_timeout")
}

/// Set `qi.eager_threshold` value to the given one.
pub fn smt_qi_eager_threshold() -> u64 {
    read_setting("smt_qi_eager_threshold")
}

/// Disable or enable the non-linear arithmetic solver by setting Z3
/// `smt.arith.nl` and `smt.arith.nl.gb` values to the given one.
pub fn smt_use_nonlinear_arithmetic_solver() -> bool {
    read_setting("smt_use_nonlinear_arithmetic_solver")
}

/// Maximum time (in milliseconds) for the verifier to spend on checks.
/// Set to None uses the verifier's default value. Maps to the verifier command-line
/// argument `--checkTimeout`.
///
/// For more information see https://github.com/viperproject/silicon/blob/4c70514379f89e7ec6f96588290ade32518f0527/src/main/scala/Config.scala#L203
pub fn check_timeout() -> Option<u32> {
    read_setting("check_timeout")
}

/// When enabled, a more complete `exhale` version is used in the verifier.
/// See [`consolidate`](https://github.com/viperproject/silicon/blob/f48de7f6e2d90d9020812869c713a5d3e2035995/src/main/scala/rules/StateConsolidator.scala#L29-L46).
/// Equivalent to the verifier command-line argument
/// `--enableMoreCompleteExhale`.
///
/// Note: This option conflicts with `use_carbon_qps`.
pub fn use_more_complete_exhale() -> bool {
    let result = read_setting("use_more_complete_exhale");
    assert!(
        !(result && read_setting::<bool>("use_carbon_qps")),
        "use_more_complete_exhale and use_carbon_qps are mutually exclusive"
    );
    result
}

/// When enabled, a Carbon QPs version of Silicon is used. Equivalent to the
/// Silicon command-line argument `--carbonQPs`.
///
/// Note: This option conflicts with `use_more_complete_exhale`.
pub fn use_carbon_qps() -> bool {
    let result = read_setting("use_carbon_qps");
    assert!(
        !(result && read_setting::<bool>("use_more_complete_exhale")),
        "use_more_complete_exhale and use_carbon_qps are mutually exclusive"
    );
    result
}

/// When enabled, Z3 is used via API.
pub fn use_z3_api() -> bool {
    read_setting("use_z3_api")
}

/// When enabled, prints the items collected for verification.
pub fn print_collected_verification_items() -> bool {
    read_setting("print_collected_verification_items")
}

/// When enabled, prints the AST with desugared specifications.
pub fn print_desugared_specs() -> bool {
    read_setting("print_desugared_specs")
}

/// When enabled, prints the type-checked specifications.
pub fn print_typeckd_specs() -> bool {
    read_setting("print_typeckd_specs")
}

/// When enabled, UUIDs of expressions and specifications printed with
/// `PRINT_TYPECKD_SPECS` are hidden.
pub fn hide_uuids() -> bool {
    read_setting("hide_uuids")
}

/// When enabled, Prusti will try to find and print a counterexample for any
/// failed assertion or specification.
pub fn counterexample() -> bool {
    read_setting("counterexample")
}

/// When enabled, Prusti will print a counterexample for a model and its original
/// type
pub fn print_counterexample_if_model_is_present() -> bool {
    read_setting("print_counterexample_if_model_is_present")
}

/// If this is set to a path, Prusti will extract the information about the
/// trace that led to the error and save it to the given file.
///
/// Note: This requires the `counterexample` and `unsafe_core_proof` options to
/// be enabled.
pub fn save_failing_trace_to_file() -> Option<String> {
    let value: Option<String> = read_setting("save_failing_trace_to_file");
    if value.is_some() {
        assert!(
            unsafe_core_proof(),
            "Unsafe core proof needs to be enabled to save failing trace to file"
        );
        assert!(
            counterexample(),
            "Counterexamples need to be enabled to save failing trace to file"
        );
    }
    value
}

/// Execute only the failing trace that was saved with
/// `save_failing_trace_to_file`. This is done by replacing all non-executed
/// basic blocks with `assume false`.
///
/// Note: This requires the `unsafe_core_proof` option to be enabled.
///
/// Note: This assumes that the program contains only a single method.
pub fn execute_only_failing_trace() -> Option<String> {
    let value: Option<String> = read_setting("execute_only_failing_trace");
    if value.is_some() {
        assert!(
            unsafe_core_proof(),
            "Unsafe core proof needs to be enabled to save failing trace to file"
        );
    }
    value
}

/// Dump additional information about the fold-unfold state of the specified
/// blocks. The blocks are expected to be generated by
/// `save_failing_trace_to_file` (and potentially edited by hand if needed).
///
/// Note: This requires the `unsafe_core_proof` option to be enabled.
///
/// Note: This assumes that the program contains only a single method.
pub fn dump_fold_unfold_state_of_blocks() -> Option<String> {
    let value: Option<String> = read_setting("dump_fold_unfold_state_of_blocks");
    if value.is_some() {
        assert!(
            unsafe_core_proof(),
            "Unsafe core proof needs to be enabled to save failing trace to file"
        );
    }
    value
}

/// When enabled, prints the hash of a verification request (the hash is used
/// for caching). This is a debugging option which does not perform
/// verification -- it is similar to `NO_VERIFY`, except that this flag stops
/// the verification process at a later stage.
pub fn print_hash() -> bool {
    read_setting("print_hash")
}

/// When enabled, verification requests (to verify individual `fn`s) are cached
/// to improve future verification. By default the cache is only saved in
/// memory (of the `prusti-server` if enabled). For long-running verification
/// projects use `CACHE_PATH` to save to disk.
pub fn enable_cache() -> bool {
    read_setting("enable_cache")
}

/// Maximum amount of instantiated Viper verifiers the server will keep around
/// for reuse. If not set, defaults to
/// `SERVER_MAX_CONCURRENT_VERIFICATION_OPERATIONS`. It also doesn't make much
/// sense to set this option to less than that, since then the server will
/// likely have to keep creating new verifiers, reducing the performance gained
/// from reuse.
///
/// **Note:** This does _not_ limit how many verification requests the server
/// handles concurrently, only the size of what is essentially its verifier
/// cache.
pub fn server_max_stored_verifiers() -> Option<usize> {
    // TODO: default to below in prusti-server
    // TODO: warn if lower than below
    read_optional_setting("server_max_stored_verifiers")
}

/// Maximum amount of verification requests the server will work on
/// concurrently. If not set, defaults to the number of (logical) cores on
/// the system.
pub fn server_max_concurrency() -> Option<usize> {
    read_optional_setting("server_max_concurrency")
}

/// When set to an address and port (e.g. `"127.0.0.1:2468"`), Prusti will
/// connect to the given server and use it for its verification backend.
///
/// When set to `"MOCK"`, the server is run off-thread, effectively mocking
/// connecting to a server without having to start it up separately.
pub fn server_address() -> Option<String> {
    read_optional_setting("server_address")
}

/// When enabled, communication with the server will be encoded as JSON
/// instead of the default bincode.
pub fn json_communication() -> bool {
    read_setting("json_communication")
}

/// When enabled, Viper name mangling will be disabled.
///
/// **Note:** This is very likely to result in invalid programs being generated
/// because of name collisions.
pub fn disable_name_mangling() -> bool {
    read_setting("disable_name_mangling")
}

/// When enabled, only the preamble will be verified: domains, functions,
/// and predicates.
///
/// **Note:** With this flag enabled, no methods are verified!
pub fn verify_only_preamble() -> bool {
    read_setting("verify_only_preamble")
}

/// When enabled, only the path given in `VERIFY_ONLY_BASIC_BLOCK_PATH` will
/// be verified.
///
/// **Note:** This flag is only for debugging Prusti.
pub fn enable_verify_only_basic_block_path() -> bool {
    read_setting("enable_verify_only_basic_block_path")
}

/// Verify only the single execution path goes through the given basic blocks.
/// All basic blocks not on this execution path are replaced with `assume false`.
/// Must be enabled using the `ENABLE_VERIFY_ONLY_BASIC_BLOCK_PATH` flag.
///
/// **Note:** This option is only for debugging Prusti.
pub fn verify_only_basic_block_path() -> Vec<String> {
    read_setting("verify_only_basic_block_path")
}

/// Comma-separated list of optimizations to enable, or `"all"` to enable all.
/// Possible values in the list are:
///
/// - `"inline_constant_functions"`
/// - `"delete_unused_predicates"`
/// - `"optimize_folding"`
/// - `"remove_empty_if"`
/// - `"purify_vars"`
/// - `"fix_quantifiers"`
/// - `"fix_unfoldings"`
/// - `"remove_unused_vars"`
/// - `"remove_trivial_assertions"`
/// - `"clean_cfg"`
pub fn optimizations() -> Optimizations {
    let optimizations_string = read_setting::<String>("optimizations");

    let mut opt = Optimizations::all_disabled();

    for s in optimizations_string.split(',') {
        let trimmed = s.trim();
        match trimmed {
            "all" => opt = Optimizations::all_enabled(),
            "inline_constant_functions" => opt.inline_constant_functions = true,
            "delete_unused_predicates" => opt.delete_unused_predicates = true,
            "optimize_folding" => opt.optimize_folding = true,
            "remove_empty_if" => opt.remove_empty_if = true,
            "purify_vars" => opt.purify_vars = true,
            "fix_quantifiers" => opt.fix_quantifiers = true,
            "fix_unfoldings" => opt.fix_unfoldings = true,
            "remove_unused_vars" => opt.remove_unused_vars = true,
            "remove_trivial_assertions" => opt.remove_trivial_assertions = true,
            "clean_cfg" => opt.clean_cfg = true,
            _ => warn!("Ignoring Unkown optimization '{}'", trimmed),
        }
    }

    opt
}

/// The Rust compiler does not guarantee that each `StorageDead` is dominated by
/// a `StorageLive`:
///
/// * https://github.com/rust-lang/rust/issues/99160
/// * https://github.com/rust-lang/rust/issues/98896
///
/// This option controls whether we should create fake `StorageLive` statements
/// in such cases.
pub fn create_missing_storage_live() -> bool {
    read_setting("create_missing_storage_live")
}

/// When enabled, impure methods are optimized using the purification
/// optimization, which tries to convert heap operations to pure (snapshot-
/// based) operations.
///
/// **Note:** this option is highly experimental.
pub fn enable_purification_optimization() -> bool {
    read_setting("enable_purification_optimization")
}

/// Deadline (in seconds) within which Prusti should encode and verify
/// the program.
///
/// Prusti panics if it fails to meet this deadline. This flag is intended to
/// be used for tests that aim to catch performance regressions.
pub fn verification_deadline() -> Option<u64> {
    read_setting::<Option<i64>>("verification_deadline").map(|value| {
        value
            .try_into()
            .expect("verification_deadline must be a valid u64")
    })
}

/// Instead of using Z3 directly, use our SMT wrapper that tracks important
/// statistics. This must be set to `true` to use any of the
/// `smt_qi_bound_*`.
pub fn use_smt_wrapper() -> bool {
    read_setting("use_smt_wrapper")
}

fn read_smt_wrapper_dependent_bool(name: &'static str) -> bool {
    let value = read_setting(name);
    if value {
        assert!(
            use_smt_wrapper(),
            "use_smt_wrapper must be true to use {name}"
        );
    }
    value
}

fn read_smt_wrapper_dependent_option(name: &'static str) -> Option<u64> {
    let value: Option<u64> = read_setting(name);
    if value.is_some() {
        assert!(
            use_smt_wrapper(),
            "use_smt_wrapper must be true to use {name}"
        );
    }
    value
}

/// Whether the built-in quantifiers should be ignored when comparing bounds.
pub fn smt_qi_ignore_builtin() -> bool {
    read_setting("smt_qi_ignore_builtin")
}

/// Limit how many quantifier instantiations Z3 can make while verifying the
/// program. This bound is for the total number of quantifier instantiations
/// made on a single thread **without** taking into account `push`/`pop`.
///
/// Z3 wrapper crashes if it exceeds this bound causing Prusti to crash as well.
/// This flag is intended to be used for tests that aim to catch performance
/// regressions and matching loops.
pub fn smt_qi_bound_global() -> Option<u64> {
    read_smt_wrapper_dependent_option("smt_qi_bound_global")
}

/// Limit how many quantifier instantiations Z3 can make while verifying the
/// program. This bound is for the total number of quantifier instantiations
/// made by a single quantifier on a single thread **without** taking into
/// account `push`/`pop`.
///
/// Z3 wrapper crashes if it exceeds this bound causing Prusti to crash as well.
/// This flag is intended to be used for tests that aim to catch performance
/// regressions and matching loops.
pub fn smt_qi_bound_global_kind() -> Option<u64> {
    read_smt_wrapper_dependent_option("smt_qi_bound_global_kind")
}

/// Limit how many quantifier instantiations Z3 can make while verifying the
/// program. This bound is for the total number of quantifier instantiations on
/// a specific trace (in other words, it is a version of
/// `smt_qi_bound_global` that takes into account `push`
/// and `pop`.)
///
/// Z3 wrapper crashes if it exceeds this bound causing Prusti to crash as well.
/// This flag is intended to be used for tests that aim to catch performance
/// regressions and matching loops.
pub fn smt_qi_bound_trace() -> Option<u64> {
    read_smt_wrapper_dependent_option("smt_qi_bound_trace")
}

/// Limit how many quantifier instantiations Z3 can make while verifying the
/// program. This bound is for the number of quantifier instantiations on a
/// specific trace per quantifier (in other words, it is a version of
/// `smt_qi_bound_trace` that takes computes the
/// instantiations for each quantifier separately.)
///
/// Z3 wrapper crashes if it exceeds this bound causing Prusti to crash as well.
/// This flag is intended to be used for tests that aim to catch performance
/// regressions and matching loops.
pub fn smt_qi_bound_trace_kind() -> Option<u64> {
    read_smt_wrapper_dependent_option("smt_qi_bound_trace_kind")
}

/// Limit how many unique triggers per quantifier Z3 can instantiate.
pub fn smt_unique_triggers_bound() -> Option<u64> {
    read_smt_wrapper_dependent_option("smt_unique_triggers_bound")
}

/// Limit how many unique triggers in total Z3 can instantiate.
pub fn smt_unique_triggers_bound_total() -> Option<u64> {
    read_smt_wrapper_dependent_option("smt_unique_triggers_bound_total")
}

/// Preserve the Z3 trace files. Since the files can be huge, they are by
/// default deleted once the required checks are made.
pub fn preserve_smt_trace_files() -> bool {
    read_smt_wrapper_dependent_bool("preserve_smt_trace_files")
}

/// Write the statistics colllected by the SMT wrapper into CSV files.
pub fn write_smt_statistics() -> bool {
    read_smt_wrapper_dependent_bool("write_smt_statistics")
}

/// Log communication of Silicon with Z3.
pub fn log_smt_wrapper_interaction() -> bool {
    read_smt_wrapper_dependent_bool("log_smt_wrapper_interaction")
}

/// When enabled, the new core proof is used, suitable for unsafe code
///
/// **Note:** This option is currently very incomplete.
pub fn unsafe_core_proof() -> bool {
    read_setting("unsafe_core_proof")
}

/// Use symbolic execution to split the procedure into traces that are verified
/// separately.
///
/// **Note:** This option is taken into account only when `unsafe_core_proof` is
/// true.
pub fn trace_with_symbolic_execution() -> bool {
    read_setting("trace_with_symbolic_execution") || purify_with_symbolic_execution()
}

pub fn trace_with_symbolic_execution_new() -> bool {
    read_setting("trace_with_symbolic_execution_new")
}

/// Use symbolic execution based purification.
///
/// **Note:** This option is taken into account only when `unsafe_core_proof` is
/// true.
///
/// **Note:** This option automatically enables
/// `trace_with_symbolic_execution`.
pub fn purify_with_symbolic_execution() -> bool {
    read_setting("purify_with_symbolic_execution")
}

/// Puts all symbolic execution traces into a single method.
///
/// **Note:** This option is taken into account only when `unsafe_core_proof` is
/// true.
pub fn symbolic_execution_single_method() -> bool {
    read_setting("symbolic_execution_single_method")
}

/// Performs predicate leak check during symbolic execution.
///
/// **Note:** This option is taken into account only when
/// `purify_with_symbolic_execution` is true.
pub fn symbolic_execution_leak_check() -> bool {
    read_setting("symbolic_execution_leak_check")
}

/// Panics if symbolic execution failed to purify out an exhale.
///
/// **Note:** This option is taken into account only when
/// `purify_with_symbolic_execution` is true.
pub fn panic_on_failed_exhale() -> bool {
    read_setting("panic_on_failed_exhale")
}

/// Panics if symbolic execution failed to purify out an exhale and it resulted
/// in a materialization of resources. In other words, if symbolic execution
/// failed to exhale an aliased resource.
///
/// **Note:** This option is taken into account only when
/// `purify_with_symbolic_execution` is true.
pub fn panic_on_failed_exhale_materialization() -> bool {
    read_setting("panic_on_failed_exhale_materialization")
}

/// If symbolic execution fails to purify out an exhale, materialize the exhale.
/// This means that the purifier will emit inhale statements for all chunks it has and an exhale statement for the chunk it failed to exhale.
///
/// **Note:** This option is taken into account only when
/// `purify_with_symbolic_execution` is true.
pub fn materialize_on_failed_exhale() -> bool {
    read_setting("materialize_on_failed_exhale")
}

/// If this option is false, purification purifies out only exhales that are
/// guaranteed to succeed because we know that on all incoming branches we have
/// the necessary heap chunk. Setting this option to `true` is sound (because we
/// still ask the verifier to check that the permission variable has the value
/// we expect on all traces), but it can lead to incompletenesses when the
/// purifier fails to merge the heap chunks due to incomplete solver.
///
/// **Note:** This option is taken into account only when
/// `purify_with_symbolic_execution` is true.
pub fn ignore_whether_exhale_is_unconditional() -> bool {
    read_setting("ignore_whether_exhale_is_unconditional")
}

/// Error when simplifying non-linear arithmetic fails.
///
/// **Note:** This option is taken into account only when
/// `purify_with_symbolic_execution` is true.
pub fn error_non_linear_arithmetic_simp() -> bool {
    read_setting("error_non_linear_arithmetic_simp")
}

/// Whether to expand the asserted quantifiers (skolemize them out).
///
/// **Note:** This option is taken into account only when `unsafe_core_proof`
/// is true.
pub fn expand_quantifiers() -> bool {
    read_setting("expand_quantifiers")
}

/// Report an error when failing to purify a predicate in symbolic execution.
///
/// **Note:** This option requires `purify_with_symbolic_execution` to be
/// enabled.
pub fn report_symbolic_execution_failures() -> bool {
    let result: bool = read_setting("report_symbolic_execution_failures");
    assert!(!result || purify_with_symbolic_execution());
    result
}

/// Add comments at the places where predicates were purified by the symbolic
/// execution.
///
/// **Note:** This option requires `purify_with_symbolic_execution` to be
/// enabled.
pub fn report_symbolic_execution_purification() -> bool {
    assert!(purify_with_symbolic_execution() || trace_with_symbolic_execution());
    read_setting("report_symbolic_execution_purification")
}

/// Use custom heap encoding.
///
/// **Note:** This option is taken into account only when `unsafe_core_proof` is
/// true.
pub fn custom_heap_encoding() -> bool {
    read_setting("custom_heap_encoding")
}

/// Whether the core proof (memory safety) should be verified.
///
/// **Note:** This option is taken into account only when `unsafe_core_proof` is
/// true.
pub fn verify_core_proof() -> bool {
    read_setting("verify_core_proof")
}

/// Whether the functional specifications should be verified.
///
/// **Note:** This option is taken into account only when `unsafe_core_proof` is
/// true.
pub fn verify_specifications() -> bool {
    read_setting("verify_specifications")
}

/// Whether the types should be verified.
///
/// **Note:** This option is taken into account only when `unsafe_core_proof` is
/// true.
pub fn verify_types() -> bool {
    read_setting("verify_types")
}

/// Whether when verifying functional specifications, the core proof should be
/// also included.
///
/// **Note:** This option is taken into account only when `unsafe_core_proof` is
/// true.
pub fn verify_specifications_with_core_proof() -> bool {
    read_setting("verify_specifications_with_core_proof")
}

/// Verification backend to use for functional specification only.
pub fn verify_specifications_backend() -> String {
    read_setting::<String>("verify_specifications_backend")
        .to_lowercase()
        .trim()
        .to_string()
}

/// Whether to generate `eval_axiom`.
///
/// **Note:** This option is taken into account only when `unsafe_core_proof` is
/// true.
pub fn use_eval_axioms() -> bool {
    read_setting("use_eval_axioms")
}

/// When enabled, inlines `caller_for` heap dependent functions.
pub fn inline_caller_for() -> bool {
    read_setting("inline_caller_for")
}

/// Whether to make the snapshot, an explicit parameter of the predicate.
///
/// **Note:** This option is taken into account only when `unsafe_core_proof` is
/// true.
pub fn use_snapshot_parameters_in_predicates() -> bool {
    read_setting("use_snapshot_parameters_in_predicates")
}

/// When enabled, replaces calls to the drop function with `assert false`.
///
/// **Note:** This option is used only for testing.
pub fn check_no_drops() -> bool {
    read_setting("check_no_drops")
}

/// When enabled, Prusti uses the new VIR encoder.
///
/// This is a temporary configuration flag.
/// The new VIR encoder is still a work in progress,
/// once finished this will become the only encoder.
///
/// If you run into `todo!()` or `unreachable!()`,
/// then setting this flag to `false` may help.
pub fn use_new_encoder() -> bool {
    read_setting("use_new_encoder")
}

/// How many parallel verifiers Silicon should use.
pub fn number_of_parallel_verifiers() -> Option<u8> {
    read_setting("number_of_parallel_verifiers")
}

/// Throw a compilation error if using a lower prusti version.
pub fn min_prusti_version() -> Option<String> {
    read_setting("min_prusti_version")
}

/// The given basic blocks will be replaced with `assume false`.
pub fn delete_basic_blocks() -> Vec<String> {
    read_setting("delete_basic_blocks")
}

/// When enabled, features not supported by Prusti will be reported as warnings
/// rather than errors.
pub fn skip_unsupported_features() -> bool {
    read_setting("skip_unsupported_features")
}

/// When enabled, internal errors are reported as warnings instead of errors.
/// Used for testing.
pub fn internal_errors_as_warnings() -> bool {
    read_setting("internal_errors_as_warnings")
}

/// When enabled, unsupported code is encoded as `assert false`. This way error
/// messages are reported only for unsupported code that is actually reachable.
pub fn allow_unreachable_unsupported_code() -> bool {
    read_setting("allow_unreachable_unsupported_code")
}

/// When enabled, verification is skipped altogether.
pub fn no_verify() -> bool {
    read_setting("no_verify")
}
pub fn set_no_verify(value: bool) {
    write_setting("no_verify", value);
}

/// When enabled, verification is skipped for dependencies.
pub fn no_verify_deps() -> bool {
    read_setting("no_verify_deps")
}

/// When enabled, verification is skipped for functions
/// that do not have the `#[verified]` attribute.
pub fn opt_in_verification() -> bool {
    read_setting("opt_in_verification")
}

/// When enabled, compilation will continue and a binary will be generated
/// after Prusti terminates.
pub fn full_compilation() -> bool {
    read_setting("full_compilation")
}

/// When enabled, Viper identifiers are interned to shorten them when possible.
pub fn intern_names() -> bool {
    read_setting("intern_names")
}

/// Determines which cargo `cargo-prusti` should run (e.g. if "cargo" isn't in
/// the path can point to it directly). Not relevant when only running as `prusti=rustc`.
pub fn cargo_path() -> String {
    read_setting("cargo_path")
}

/// Determines which command `cargo-prusti` should run (default is "check"
/// for `cargo check`). Not relevant when only running as `prusti=rustc`.
pub fn cargo_command() -> String {
    read_setting("cargo_command")
}

/// When enabled, type invariants can be declared on types using the
/// `#[invariant(...)]` attribute.
pub fn enable_type_invariants() -> bool {
    read_setting("enable_type_invariants")
}
