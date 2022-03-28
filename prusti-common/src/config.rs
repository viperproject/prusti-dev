// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![allow(deprecated)]

pub mod commandline;

use self::commandline::CommandLine;
use config_crate::{Config, Environment, File};
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

lazy_static! {
    // Is this RwLock<..> necessary?
    static ref SETTINGS: RwLock<Config> = RwLock::new({
        let mut settings = Config::default();

        // 1. Default values
        settings.set_default("be_rustc", false).unwrap();
        settings.set_default("viper_backend", "Silicon").unwrap();
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
        settings.set_default("use_more_complete_exhale", true).unwrap();
        settings.set_default("skip_unsupported_features", false).unwrap();
        settings.set_default("internal_errors_as_warnings", false).unwrap();
        settings.set_default("allow_unreachable_unsupported_code", false).unwrap();
        settings.set_default("no_verify", false).unwrap();
        settings.set_default("no_verify_deps", false).unwrap();
        settings.set_default("full_compilation", false).unwrap();
        settings.set_default("json_communication", false).unwrap();
        settings.set_default("optimizations","all").unwrap();
        settings.set_default("intern_names", true).unwrap();
        settings.set_default("enable_purification_optimization", false).unwrap();
        settings.set_default("enable_manual_axiomatization", false).unwrap();
        settings.set_default::<Option<i64>>("verification_deadline", None).unwrap();
        settings.set_default("unsafe_core_proof", false).unwrap();
        settings.set_default("only_memory_safety", false).unwrap();

        settings.set_default("print_desugared_specs", false).unwrap();
        settings.set_default("print_typeckd_specs", false).unwrap();
        settings.set_default("print_collected_verification_items", false).unwrap();
        settings.set_default("hide_uuids", false).unwrap();
        settings.set_default("counterexample", false).unwrap();
        settings.set_default("print_hash", false).unwrap();
        settings.set_default("enable_cache", true).unwrap();

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
            Environment::with_prefix("PRUSTI").ignore_empty(true)
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
    format!("{:#?}", SETTINGS.read().unwrap())
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
    read_optional_setting(name).unwrap_or_else(|| panic!("Failed to read setting {:?}", name))
}

/// Should Prusti behave exactly like rustc?
pub fn be_rustc() -> bool {
    read_setting("be_rustc")
}

/// Generate additional, *slow*, checks for the foldunfold algorithm
pub fn check_foldunfold_state() -> bool {
    read_setting("check_foldunfold_state")
}

/// The Viper backend that should be used for the verification
pub fn viper_backend() -> String {
    read_setting::<String>("viper_backend")
        .to_lowercase()
        .trim()
        .to_string()
}

/// Should we check absence of panics?
pub fn check_panics() -> bool {
    read_setting("check_panics")
}

/// Should we simplify the encoding before passing it to Viper?
pub fn simplify_encoding() -> bool {
    read_setting("simplify_encoding")
}

/// Should we dump debug files?
pub fn dump_debug_info() -> bool {
    read_setting("dump_debug_info")
}

/// Should we dump debug files for fold/unfold generation?
pub fn dump_debug_info_during_fold() -> bool {
    read_setting("dump_debug_info_during_fold")
}

/// Should the dumped debug files not contain lifetime regions?
pub fn ignore_regions() -> bool {
    read_setting("ignore_regions")
}

/// What is the longest allowed length of a log file name? If this is exceeded,
/// the file name is truncated.
pub fn max_log_file_name_length() -> usize {
    read_setting("max_log_file_name_length")
}

/// Should we dump the branch context state in debug files?
pub fn dump_path_ctxt_in_debug_info() -> bool {
    read_setting("dump_path_ctxt_in_debug_info")
}

/// Should we dump the reborrowing DAGs in debug files?
pub fn dump_reborrowing_dag_in_debug_info() -> bool {
    read_setting("dump_reborrowing_dag_in_debug_info")
}

/// Should we dump borrowck info?
pub fn dump_borrowck_info() -> bool {
    read_setting("dump_borrowck_info")
}

/// Should we dump the Viper program?
pub fn dump_viper_program() -> bool {
    read_setting("dump_viper_program")
}

/// The Viper backend that should be used for the verification
pub fn foldunfold_state_filter() -> String {
    read_setting("foldunfold_state_filter")
}

/// In which folder should we store log/dumps?
pub fn log_dir() -> PathBuf {
    PathBuf::from(read_setting::<String>("log_dir"))
}

/// In which folder should we store the Verification cache
pub fn cache_path() -> PathBuf {
    PathBuf::from(read_setting::<String>("cache_path"))
}

/// Check binary operations for overflows
pub fn check_overflows() -> bool {
    read_setting("check_overflows")
}

/// Encode (and check) that unsigned integers are non-negative.
pub fn encode_unsigned_num_constraint() -> bool {
    read_setting("encode_unsigned_num_constraint")
}

/// Enable (highly hacky) support for bitvectors.
pub fn encode_bitvectors() -> bool {
    read_setting("encode_bitvectors")
}

/// Location of 'libprusti_contracts*.rlib'
pub fn contracts_lib() -> String {
    read_setting("contracts_lib")
}

/// Get extra JVM arguments
pub fn extra_jvm_args() -> Vec<String> {
    read_setting("extra_jvm_args")
}

/// Get extra arguments for the verifier
pub fn extra_verifier_args() -> Vec<String> {
    read_setting("extra_verifier_args")
}

/// Should we hide user messages?
pub fn quiet() -> bool {
    read_setting("quiet")
}

/// The assert timeout (in milliseconds) passed to Silicon.
pub fn assert_timeout() -> u64 {
    read_setting("assert_timeout")
}

/// Use the Silicon configuration option `--enableMoreCompleteExhale`.
pub fn use_more_complete_exhale() -> bool {
    read_setting("use_more_complete_exhale")
}

/// Should Prusti print the items collected for verification.
pub fn print_collected_verification_items() -> bool {
    read_setting("print_collected_verification_items")
}

/// Should Prusti print the AST with desugared specifications.
pub fn print_desugared_specs() -> bool {
    read_setting("print_desugared_specs")
}

/// Should Prusti print the type-checked specifications.
pub fn print_typeckd_specs() -> bool {
    read_setting("print_typeckd_specs")
}

/// Should Prusti hide the UUIDs of expressions and specifications.
pub fn hide_uuids() -> bool {
    read_setting("hide_uuids")
}

/// Should Prusti produce a counterexample.
pub fn produce_counterexample() -> bool {
    read_setting("counterexample")
}

/// Should Prusti print VerificationRequest hashes.
pub fn print_hash() -> bool {
    read_setting("print_hash")
}

/// Should Prusti ignore cached verification results.
pub fn enable_cache() -> bool {
    read_setting("enable_cache")
}

/**
The maximum amount of instantiated viper verifiers the server will keep around for reuse.
If not set, this defaults to `SERVER_MAX_CONCURRENT_VERIFICATION_OPERATIONS`.
It also doesn't make much sense to set this to less than that, since then the server will likely have to keep creating new verifiers, reducing the performance gained from reuse.
**Note:** This does _not_ limit how many verification requests the server handles concurrently, only the size of what is essentially its verifier cache.
*/
pub fn server_max_stored_verifiers() -> Option<usize> {
    // TODO: default to below in prusti-server
    // TODO: warn if lower than below
    read_optional_setting("server_max_stored_verifiers")
}

/// The maximum amount of verification requests the server will work on concurrently.
///
/// If not set, this defaults to the number of (logical) cores on the system
pub fn server_max_concurrency() -> Option<usize> {
    read_optional_setting("server_max_concurrency")
}

/// When set, Prusti will connect to this server and use it for its verification backend (i.e. the things using the JVM/Viper).
/// Set to "MOCK" to run the server off-thread, effectively mocking connecting to a server without having to start it up separately.
/// e.g. "127.0.0.1:2468"
pub fn server_address() -> Option<String> {
    read_optional_setting("server_address")
}

/// If true, communication with the server will be encoded as json and not the default of bincode.
pub fn json_communication() -> bool {
    read_setting("json_communication")
}

/// Disable mangling of generated Viper names.
///
/// **Note:** This is very likely to result in invalid programs being
/// generated because of name collisions.
pub fn disable_name_mangling() -> bool {
    read_setting("disable_name_mangling")
}

/// Verify only the preamble: domains, functions, and predicates.
///
/// **Note:** With this flag enabled, no methods are verified!
pub fn verify_only_preamble() -> bool {
    read_setting("verify_only_preamble")
}

/// Verify only the path given in ``VERIFY_ONLY_BASIC_BLOCK_PATH``.
///
/// **Note:** This flag is only for debugging Prusti!
pub fn enable_verify_only_basic_block_path() -> bool {
    read_setting("enable_verify_only_basic_block_path")
}

/// Verify only the single execution path goes through the given basic blocks.
///
/// All basic blocks not on this execution path are replaced with
/// ``assume false``.
///
/// **Note:** This flag is only for debugging Prusti!
pub fn verify_only_basic_block_path() -> Vec<String> {
    read_setting("verify_only_basic_block_path")
}

/// Which optimizations should be enabled
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

/// Enable purification optimization for impure functions.
pub fn enable_purification_optimization() -> bool {
    read_setting("enable_purification_optimization")
}

/// Enable manual axiomatization of pure functions.
///
/// **Note:** this is currently very incomplete and may introduce unsoudnesses.
pub fn enable_manual_axiomatization() -> bool {
    read_setting("enable_manual_axiomatization")
}

/// Set the deadline in seconds within which Prusti should encode and verify the
/// program.
///
/// Prusti panics if it fails to meet this deadline. This flag is intended to be
/// used for tests that aim to catch performance regressions.
pub fn verification_deadline() -> Option<u64> {
    read_setting::<Option<i64>>("verification_deadline").map(|value| {
        value.try_into().expect("verification_deadline must be a valid u64")
    })
}

/// Use the new core proof suitable for unsafe code.
///
/// **Note:** this is currently very incomplete.
pub fn unsafe_core_proof() -> bool {
    read_setting("unsafe_core_proof")
}

/// Verify only the core proof.
///
/// Note: This should be used together with `unsafe_core_proof=True`.
pub fn only_memory_safety() -> bool {
    read_setting("only_memory_safety")
}

/// Replace the given basic blocks with ``assume false``.
pub fn delete_basic_blocks() -> Vec<String> {
    read_setting("delete_basic_blocks")
}

/// Skip features that are unsupported or partially supported
pub fn skip_unsupported_features() -> bool {
    read_setting("skip_unsupported_features")
}

/// Report internal errors as warnings instead of errors. Used for testing.
pub fn internal_errors_as_warnings() -> bool {
    read_setting("internal_errors_as_warnings")
}

/// Encode unsupported code as `assert false`, so that we report error messages
/// only for unsupported code that is actually reachable.
pub fn allow_unreachable_unsupported_code() -> bool {
    read_setting("allow_unreachable_unsupported_code")
}

/// Skip the verification
pub fn no_verify() -> bool {
    read_setting("no_verify")
}

/// Skip the verification of dependencies
pub fn no_verify_deps() -> bool {
    read_setting("no_verify_deps")
}

/// Continue the compilation and generate the binary after Prusti terminates
pub fn full_compilation() -> bool {
    read_setting("full_compilation")
}

/// Intern Viper identifiers to shorten them when possible.
pub fn intern_names() -> bool {
    read_setting("intern_names")
}
