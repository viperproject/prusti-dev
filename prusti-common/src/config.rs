// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod commandline;

use config_crate::{Config, Environment, File};
use self::commandline::CommandLine;
use std::env;
use std::sync::RwLock;
use serde::Deserialize;


#[derive(Debug, PartialEq, Eq)]
pub struct Optimizations {
    pub inline_constant_functions: bool,
    pub delete_unused_predicates: bool,
    pub optimize_folding: bool,
    pub remove_empty_if: bool,
    pub purify_vars: bool,
    pub fix_quantifiers: bool,
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
            remove_unused_vars: false,
            remove_trivial_assertions: false,
            clean_cfg: false,
        }
    }

    fn all_enabled() -> Self {
        Optimizations{
            inline_constant_functions: true,
            delete_unused_predicates: true,
            optimize_folding: true,
            remove_empty_if: true,
            purify_vars: true,
            fix_quantifiers: true,
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
        settings.set_default("BE_RUSTC", false).unwrap();
        settings.set_default("VIPER_BACKEND", "Silicon").unwrap();
        settings.set_default("CHECK_FOLDUNFOLD_STATE", false).unwrap();
        settings.set_default("CHECK_OVERFLOWS", false).unwrap();
        settings.set_default("CHECK_PANICS", true).unwrap();
        settings.set_default("ENCODE_UNSIGNED_NUM_CONSTRAINT", false).unwrap();
        settings.set_default("SIMPLIFY_ENCODING", true).unwrap();
        settings.set_default("LOG_DIR", "./log/").unwrap();
        settings.set_default("DUMP_DEBUG_INFO", false).unwrap();
        settings.set_default("DUMP_DEBUG_INFO_DURING_FOLD", false).unwrap();
        settings.set_default("MAX_LOG_FILE_NAME_LENGTH", 60).unwrap();
        settings.set_default("DUMP_PATH_CTXT_IN_DEBUG_INFO", false).unwrap();
        settings.set_default("DUMP_REBORROWING_DAG_IN_DEBUG_INFO", false).unwrap();
        settings.set_default("DUMP_BORROWCK_INFO", false).unwrap();
        settings.set_default("DUMP_VIPER_PROGRAM", false).unwrap();
        settings.set_default("FOLDUNFOLD_STATE_FILTER", "").unwrap();
        settings.set_default("CONTRACTS_LIB", "").unwrap();
        settings.set_default::<Vec<String>>("EXTRA_JVM_ARGS", vec![]).unwrap();
        settings.set_default::<Vec<String>>("EXTRA_VERIFIER_ARGS", vec![]).unwrap();
        settings.set_default("QUIET", false).unwrap();
        settings.set_default("ASSERT_TIMEOUT", 10_000).unwrap();
        settings.set_default("USE_MORE_COMPLETE_EXHALE", true).unwrap();
        settings.set_default("SKIP_UNSUPPORTED_FEATURES", false).unwrap();
        settings.set_default("ALLOW_UNREACHABLE_UNSUPPORTED_CODE", false).unwrap();
        settings.set_default("NO_VERIFY", false).unwrap();
        settings.set_default("FULL_COMPILATION", false).unwrap();
        settings.set_default("JSON_COMMUNICATION", false).unwrap();
        settings.set_default("JSON_COMMUNICATION", false).unwrap();
        settings.set_default("OPTIMIZATIONS","all").unwrap();
        settings.set_default("INTERN_NAMES", true).unwrap();

        settings.set_default("PRINT_DESUGARED_SPECS", false).unwrap();
        settings.set_default("PRINT_TYPECKD_SPECS", false).unwrap();
        settings.set_default("PRINT_COLLECTED_VERIFICATION_ITEMS", false).unwrap();
        settings.set_default("HIDE_UUIDS", false).unwrap();
        
        // Flags for debugging Prusti that can change verification results.
        settings.set_default("DISABLE_NAME_MANGLING", false).unwrap();
        settings.set_default("VERIFY_ONLY_PREAMBLE", false).unwrap();
        settings.set_default("ENABLE_VERIFY_ONLY_BASIC_BLOCK_PATH", false).unwrap();
        settings.set_default::<Vec<String>>("VERIFY_ONLY_BASIC_BLOCK_PATH", vec![]).unwrap();
        settings.set_default::<Vec<String>>("DELETE_BASIC_BLOCKS", vec![]).unwrap();


        // 2. Override with the optional TOML file "Prusti.toml" (if there is any)
        settings.merge(
            File::with_name("Prusti.toml").required(false)
        ).unwrap();

        // 3. Override with an optional TOML file specified by the `PRUSTI_CONFIG` env variable
        settings.merge(
            File::with_name(&env::var("PRUSTI_CONFIG").unwrap_or("".to_string())).required(false)
        ).unwrap();

        // 4. Override with env variables (`PRUSTI_VIPER_BACKEND`, ...)
        settings.merge(
            Environment::with_prefix("PRUSTI").ignore_empty(true)
        ).unwrap();

        // 5. Override with command-line arguments -P<arg>=<val>
        settings.merge(
            CommandLine::with_prefix("-P").ignore_invalid(true)
        ).unwrap();

        settings
    });
}

/// Return vector of arguments filtered out by prefix
pub fn get_filtered_args() -> Vec<String> {
    CommandLine::with_prefix("-P")
        .get_remaining_args()
        .collect::<Vec<String>>()
}

/// Generate a dump of the settings
pub fn dump() -> String {
    format!("{:?}", SETTINGS.read().unwrap())
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
    read_optional_setting(name).unwrap()
}

/// Should Prusti behave exactly like rustc?
pub fn be_rustc() -> bool {
    read_setting("BE_RUSTC")
}

/// Generate additional, *slow*, checks for the foldunfold algorithm
pub fn check_foldunfold_state() -> bool {
    read_setting("CHECK_FOLDUNFOLD_STATE")
}

/// The Viper backend that should be used for the verification
pub fn viper_backend() -> String {
    read_setting::<String>("VIPER_BACKEND")
        .to_lowercase()
        .trim()
        .to_string()
}

/// Should we check absence of panics?
pub fn check_panics() -> bool {
    read_setting("CHECK_PANICS")
}

/// Should we simplify the encoding before passing it to Viper?
pub fn simplify_encoding() -> bool {
    read_setting("SIMPLIFY_ENCODING")
}

/// Should we dump debug files?
pub fn dump_debug_info() -> bool {
    read_setting("DUMP_DEBUG_INFO")
}

/// Should we dump debug files for fold/unfold generation?
pub fn dump_debug_info_during_fold() -> bool {
    read_setting("DUMP_DEBUG_INFO_DURING_FOLD")
}

/// What is the longest allowed length of a log file name? If this is exceeded,
/// the file name is truncated.
pub fn max_log_file_name_length() -> usize {
    read_setting("MAX_LOG_FILE_NAME_LENGTH")
}

/// Should we dump the branch context state in debug files?
pub fn dump_path_ctxt_in_debug_info() -> bool {
    read_setting("DUMP_PATH_CTXT_IN_DEBUG_INFO")
}

/// Should we dump the reborrowing DAGs in debug files?
pub fn dump_reborrowing_dag_in_debug_info() -> bool {
    read_setting("DUMP_REBORROWING_DAG_IN_DEBUG_INFO")
}

/// Should we dump borrowck info?
pub fn dump_borrowck_info() -> bool {
    read_setting("DUMP_BORROWCK_INFO")
}

/// Should we dump the Viper program?
pub fn dump_viper_program() -> bool {
    read_setting("DUMP_VIPER_PROGRAM")
}

/// The Viper backend that should be used for the verification
pub fn foldunfold_state_filter() -> String {
    read_setting("FOLDUNFOLD_STATE_FILTER")
}

/// In which folder should we sore log/dumps?
pub fn log_dir() -> String {
    read_setting("LOG_DIR")
}

/// Check binary operations for overflows
pub fn check_overflows() -> bool {
    read_setting("CHECK_OVERFLOWS")
}

/// Encode (and check) that unsigned integers are non-negative.
pub fn encode_unsigned_num_constraint() -> bool {
    read_setting("ENCODE_UNSIGNED_NUM_CONSTRAINT")
}

/// Location of 'libprusti_contracts*.rlib'
pub fn contracts_lib() -> String {
    read_setting("CONTRACTS_LIB")
}

/// Get extra JVM arguments
pub fn extra_jvm_args() -> Vec<String> {
    read_setting("EXTRA_JVM_ARGS")
}

/// Get extra arguments for the verifier
pub fn extra_verifier_args() -> Vec<String> {
    read_setting("EXTRA_VERIFIER_ARGS")
}

/// Should we hide user messages?
pub fn quiet() -> bool {
    read_setting("QUIET")
}

/// The assert timeout (in milliseconds) passed to Silicon.
pub fn assert_timeout() -> u64 {
    read_setting("ASSERT_TIMEOUT")
}

/// Use the Silicon configuration option `--enableMoreCompleteExhale`.
pub fn use_more_complete_exhale() -> bool {
    read_setting("USE_MORE_COMPLETE_EXHALE")
}

/// Should Prusti print the items collected for verification.
pub fn print_collected_verification_items() -> bool {
    read_setting("PRINT_COLLECTED_VERIFICATION_ITEMS")
}

/// Should Prusti print the AST with desugared specifications.
pub fn print_desugared_specs() -> bool {
    read_setting("PRINT_DESUGARED_SPECS")
}

/// Should Prusti print the type-checked specifications.
pub fn print_typeckd_specs() -> bool {
    read_setting("PRINT_TYPECKD_SPECS")
}

/// Should Prusti hide the UUIDs of expressions and specifications.
pub fn hide_uuids() -> bool {
    read_setting("HIDE_UUIDS")
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
    read_optional_setting("SERVER_MAX_STORED_VERIFIERS")
}

/// The maximum amount of verification requests the server will work on concurrently.
///
/// If not set, this defaults to the number of (logical) cores on the system
pub fn server_max_concurrency() -> Option<usize> {
    read_optional_setting("SERVER_MAX_CONCURRENCY")
}

/// When set, Prusti will connect to this server and use it for its verification backend (i.e. the things using the JVM/Viper).
/// Set to "MOCK" to run the server off-thread, effectively mocking connecting to a server without having to start it up separately.
/// e.g. "127.0.0.1:2468"
pub fn server_address() -> Option<String> {
    read_optional_setting("SERVER_ADDRESS")
}

/// If true, communication with the server will be encoded as json and not the default of bincode.
pub fn json_communication() -> bool {
    read_setting("JSON_COMMUNICATION")
}

/// Disable mangling of generated Viper names.
///
/// **Note:** This is very likely to result in invalid programs being
/// generated because of name collisions.
pub fn disable_name_mangling() -> bool {
    read_setting("DISABLE_NAME_MANGLING")
}

/// Verify only the preamble: domains, functions, and predicates.
///
/// **Note:** With this flag enabled, no methods are verified!
pub fn verify_only_preamble() -> bool {
    read_setting("VERIFY_ONLY_PREAMBLE")
}

/// Verify only the path given in ``VERIFY_ONLY_BASIC_BLOCK_PATH``.
///
/// **Note:** This flag is only for debugging Prusti!
pub fn enable_verify_only_basic_block_path() -> bool {
    read_setting("ENABLE_VERIFY_ONLY_BASIC_BLOCK_PATH")
}

/// Verify only the single execution path goes through the given basic blocks.
///
/// All basic blocks not on this execution path are replaced with
/// ``assume false``.
///
/// **Note:** This flag is only for debugging Prusti!
pub fn verify_only_basic_block_path() -> Vec<String> {
    read_setting("VERIFY_ONLY_BASIC_BLOCK_PATH")
}

/// Which optimizations should be enabled
pub fn optimizations() -> Optimizations {
    let optimizations_string = read_setting::<String>("OPTIMIZATIONS");

    let mut opt = Optimizations::all_disabled();

    for s in optimizations_string.split(","){
        let trimmed = s.trim();
        match trimmed {
            "all" => opt = Optimizations::all_enabled(),
            "inline_constant_functions" => opt.inline_constant_functions = true,
            "delete_unused_predicates" => opt.delete_unused_predicates = true,
            "optimize_folding" => opt.optimize_folding = true,
            "remove_empty_if" => opt.remove_empty_if = true,
            "purify_vars" => opt.purify_vars = true,
            "fix_quantifiers" => opt.fix_quantifiers = true,
            "remove_unused_vars" => opt.remove_unused_vars = true,
            "remove_trivial_assertions" => opt.remove_trivial_assertions = true,
            "clean_cfg" => opt.clean_cfg = true,
            _ => warn!("Ignoring Unkown optimization '{}'", trimmed)
        }
    }

    return opt;
}

/// Replace the given basic blocks with ``assume false``.
pub fn delete_basic_blocks() -> Vec<String> {
    read_setting("DELETE_BASIC_BLOCKS")
}

/// Skip features that are unsupported or partially supported
pub fn skip_unsupported_features() -> bool {
    read_setting("SKIP_UNSUPPORTED_FEATURES")
}

/// Encode unsupported code as `assert false`, so that we report error messages
/// only for unsupported code that is actually reachable.
pub fn allow_unreachable_unsupported_code() -> bool {
    read_setting("ALLOW_UNREACHABLE_UNSUPPORTED_CODE")
}

/// Skip the verification
pub fn no_verify() -> bool {
    read_setting("NO_VERIFY")
}

/// Continue the compilation and generate the binary after Prusti terminates
pub fn full_compilation() -> bool {
    read_setting("FULL_COMPILATION")
}

/// Intern Viper identifiers to shorten them when possible.
pub fn intern_names() -> bool {
    read_setting("INTERN_NAMES")
}
