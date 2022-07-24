// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![allow(deprecated)]

pub mod commandline;

use self::commandline::CommandLine;
use ::config::{Config, Environment, File};
use log::warn;
use prusti_launch::{get_current_executable_dir, find_viper_home};
use serde::Deserialize;
use std::{collections::HashSet, env, path::PathBuf, sync::RwLock};

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

        // 1. Default values
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
        settings.set_default("encode_unsigned_num_constraint", false).unwrap();
        settings.set_default("encode_bitvectors", false).unwrap();
        settings.set_default("simplify_encoding", true).unwrap();
        settings.set_default("log_dir", "log").unwrap();
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
        settings.set_default("contracts_lib", "").unwrap();
        settings.set_default::<Vec<String>>("extra_jvm_args", vec![]).unwrap();
        settings.set_default::<Vec<String>>("extra_verifier_args", vec![]).unwrap();
        settings.set_default("quiet", false).unwrap();
        settings.set_default("assert_timeout", 10_000).unwrap();
        settings.set_default("smt_qi_eager_threshold", 1000).unwrap();
        settings.set_default("use_more_complete_exhale", true).unwrap();
        settings.set_default("skip_unsupported_features", false).unwrap();
        settings.set_default("internal_errors_as_warnings", false).unwrap();
        settings.set_default("allow_unreachable_unsupported_code", false).unwrap();
        settings.set_default("no_verify", false).unwrap();
        settings.set_default("no_verify_deps", false).unwrap();
        settings.set_default("full_compilation", false).unwrap();
        settings.set_default("json_communication", false).unwrap();
        settings.set_default("optimizations", "all").unwrap();
        settings.set_default("intern_names", true).unwrap();
        settings.set_default("enable_purification_optimization", false).unwrap();
        // settings.set_default("enable_manual_axiomatization", false).unwrap();
        settings.set_default("unsafe_core_proof", false).unwrap();
        settings.set_default("verify_core_proof", true).unwrap();
        settings.set_default("verify_specifications", true).unwrap();
        settings.set_default("verify_specifications_with_core_proof", false).unwrap();
        settings.set_default("verify_specifications_backend", "Silicon").unwrap();
        settings.set_default("inline_caller_for", false).unwrap();
        settings.set_default("check_no_drops", false).unwrap();
        settings.set_default("enable_type_invariants", false).unwrap();
        settings.set_default("use_new_encoder", true).unwrap();
        settings.set_default::<Option<u8>>("number_of_parallel_verifiers", None).unwrap();

        settings.set_default("print_desugared_specs", false).unwrap();
        settings.set_default("print_typeckd_specs", false).unwrap();
        settings.set_default("print_collected_verification_items", false).unwrap();
        settings.set_default("hide_uuids", false).unwrap();
        settings.set_default("counterexample", false).unwrap();
        settings.set_default("print_hash", false).unwrap();
        settings.set_default("enable_cache", true).unwrap();
        settings.set_default("enable_ghost_constraints", false).unwrap();

        // Flags for testing.
        settings.set_default::<Option<i64>>("verification_deadline", None).unwrap();
        settings.set_default("use_smt_wrapper", false).unwrap();
        settings.set_default("smt_quantifier_instantiations_ignore_builtin", true).unwrap();
        settings.set_default::<Option<u64>>("smt_quantifier_instantiations_bound_global", None).unwrap();
        settings.set_default::<Option<u64>>("smt_quantifier_instantiations_bound_global_kind", None).unwrap();
        settings.set_default::<Option<u64>>("smt_quantifier_instantiations_bound_trace", None).unwrap();
        settings.set_default::<Option<u64>>("smt_quantifier_instantiations_bound_trace_kind", None).unwrap();
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

        // 2. Override with default env variables (e.g. `DEFAULT_PRUSTI_CACHE_PATH`, ...)
        settings.merge(
            Environment::with_prefix("DEFAULT_PRUSTI").ignore_empty(true)
        ).unwrap();
        check_keys(&settings, &allowed_keys, "default environment variables");

        // 3. Override with an optional TOML file specified by the `PRUSTI_CONFIG` env variable
        let file = env::var("PRUSTI_CONFIG").unwrap_or_else(|_| "./Prusti.toml".to_string());
        // Since this file may explicitly be specified by the user, it would be
        // nice to tell them if we cannot open it.
        settings.merge(File::with_name(&file).required(false)).unwrap();
        check_keys(&settings, &allowed_keys, &format!("{} file", file));

        // 4. Override with env variables (`PRUSTI_VIPER_BACKEND`, ...)
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

        // 5. Override with command-line arguments -P<arg>=<val>
        settings.merge(
            CommandLine::with_prefix("-P").ignore_invalid(true)
        ).unwrap();
        check_keys(&settings, &allowed_keys, "command line arguments");

        settings
    });
}

fn get_keys(settings: &Config) -> HashSet<String> {
    settings
        .cache
        .clone()
        .into_table()
        .unwrap()
        .into_iter()
        .map(|(key, _)| key)
        .collect()
}

fn check_keys(settings: &Config, allowed_keys: &HashSet<String>, source: &str) {
    for key in settings.cache.clone().into_table().unwrap().keys() {
        assert!(
            allowed_keys.contains(key),
            "{} contains unknown configuration flag: “{}”",
            source,
            key
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
    let mut pairs: Vec<_> = map.iter().map(|(key, value)| format!("{}={:#?}", key, value)).collect();
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
    SETTINGS.read().unwrap().get(name).unwrap_or_else(|e| panic!("Failed to read setting {} due to {}", name, e))
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
pub fn viper_backend() -> viper::VerificationBackend {
    let verification_backend_name = read_setting::<String>("viper_backend")
        .to_lowercase()
        .trim()
        .to_string();
    <viper::VerificationBackend as std::str::FromStr>::from_str(&verification_backend_name).unwrap()
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

/// Path to directory in which log files and dumped output will be stored.
pub fn log_dir() -> PathBuf {
    PathBuf::from(read_setting::<String>("log_dir"))
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

/// Path to `libprusti_contracts*.rlib`.
pub fn contracts_lib() -> String {
    read_setting("contracts_lib")
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
pub fn use_more_complete_exhale() -> bool {
    read_setting("use_more_complete_exhale")
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
        value.try_into().expect("verification_deadline must be a valid u64")
    })
}

/// Instead of using Z3 directly, use our SMT wrapper that tracks important
/// statistics. This must be set to `true` to use any of the
/// `smt_quantifier_instantiations_bound_*`.
pub fn use_smt_wrapper() -> bool {
    read_setting("use_smt_wrapper")
}

fn read_smt_wrapper_dependent_bool(name: &'static str) -> bool
{
    let value = read_setting(name);
    if value {
        assert!(use_smt_wrapper(), "use_smt_wrapper must be true to use {}", name);
    }
    value
}

fn read_smt_wrapper_dependent_option(name: &'static str) -> Option<u64>
{
    let value: Option<u64> = read_setting(name);
    if value.is_some() {
        assert!(use_smt_wrapper(), "use_smt_wrapper must be true to use {}", name);
    }
    value
}

/// Whether the built-in quantifiers should be ignored when comparing bounds.
pub fn smt_quantifier_instantiations_ignore_builtin() -> bool {
    read_setting("smt_quantifier_instantiations_ignore_builtin")
}

/// Limit how many quantifier instantiations Z3 can make while verifying the
/// program. This bound is for the total number of quantifier instantiations
/// made on a single thread **without** taking into account `push`/`pop`.
///
/// Z3 wrapper crashes if it exceeds this bound causing Prusti to crash as well.
/// This flag is intended to be used for tests that aim to catch performance
/// regressions and matching loops.
pub fn smt_quantifier_instantiations_bound_global() -> Option<u64> {
    read_smt_wrapper_dependent_option("smt_quantifier_instantiations_bound_global")
}

/// Limit how many quantifier instantiations Z3 can make while verifying the
/// program. This bound is for the total number of quantifier instantiations
/// made by a single quantifier on a single thread **without** taking into
/// account `push`/`pop`.
///
/// Z3 wrapper crashes if it exceeds this bound causing Prusti to crash as well.
/// This flag is intended to be used for tests that aim to catch performance
/// regressions and matching loops.
pub fn smt_quantifier_instantiations_bound_global_kind() -> Option<u64> {
    read_smt_wrapper_dependent_option("smt_quantifier_instantiations_bound_global_kind")
}

/// Limit how many quantifier instantiations Z3 can make while verifying the
/// program. This bound is for the total number of quantifier instantiations on
/// a specific trace (in other words, it is a version of
/// `smt_quantifier_instantiations_bound_global` that takes into account `push`
/// and `pop`.)
///
/// Z3 wrapper crashes if it exceeds this bound causing Prusti to crash as well.
/// This flag is intended to be used for tests that aim to catch performance
/// regressions and matching loops.
pub fn smt_quantifier_instantiations_bound_trace() -> Option<u64> {
    read_smt_wrapper_dependent_option("smt_quantifier_instantiations_bound_trace")
}

/// Limit how many quantifier instantiations Z3 can make while verifying the
/// program. This bound is for the number of quantifier instantiations on a
/// specific trace per quantifier (in other words, it is a version of
/// `smt_quantifier_instantiations_bound_trace` that takes computes the
/// instantiations for each quantifier separately.)
///
/// Z3 wrapper crashes if it exceeds this bound causing Prusti to crash as well.
/// This flag is intended to be used for tests that aim to catch performance
/// regressions and matching loops.
pub fn smt_quantifier_instantiations_bound_trace_kind() -> Option<u64> {
    read_smt_wrapper_dependent_option("smt_quantifier_instantiations_bound_trace_kind")
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

/// Whether the core proof (memory safety) should be verified.
///
/// **Note:** This option is taken into account only when `unsafe_core_proof` to
/// be true.
pub fn verify_core_proof() -> bool {
    read_setting("verify_core_proof")
}

/// Whether the functional specifications should be verified.
///
/// **Note:** This option is taken into account only when `unsafe_core_proof` to
/// be true.
pub fn verify_specifications() -> bool {
    read_setting("verify_specifications")
}

/// Whether when verifying functional specifications, the core proof should be
/// also included.
///
/// **Note:** This option is taken into account only when `unsafe_core_proof` to
/// be true.
pub fn verify_specifications_with_core_proof() -> bool {
    read_setting("verify_specifications_with_core_proof")
}

/// Verification backend to use for functional specification only.
pub fn verify_specifications_backend() -> viper::VerificationBackend {
    let verification_backend_name = read_setting::<String>("verify_specifications_backend")
        .to_lowercase()
        .trim()
        .to_string();
    <viper::VerificationBackend as std::str::FromStr>::from_str(&verification_backend_name).unwrap()
}

/// When enabled, inlines `caller_for` heap dependent functions.
pub fn inline_caller_for() -> bool {
    read_setting("inline_caller_for")
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

/// When enabled, verification is skipped for dependencies.
pub fn no_verify_deps() -> bool {
    read_setting("no_verify_deps")
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

/// When enabled, ghost constraints can be used in Prusti specifications.
///
/// Ghost constraints allow for specifications which are only active if a
/// certain "constraint" (i.e. a trait bound on a generic type parameter) is
/// satisfied.
///
/// **This is an experimental feature**, because it is currently possible to
/// introduce unsound verification behavior.
pub fn enable_ghost_constraints() -> bool {
    read_setting("enable_ghost_constraints")
}

/// When enabled, type invariants can be declared on types using the
/// `#[invariant(...)]` attribute.
pub fn enable_type_invariants() -> bool {
    read_setting("enable_type_invariants")
}
