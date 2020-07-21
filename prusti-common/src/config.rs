// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use config_crate::{Config, Environment, File};
use serde::Deserialize;
use std::{env, sync::RwLock};

lazy_static! {
    // Is this RwLock<..> necessary?
    static ref SETTINGS: RwLock<Config> = RwLock::new({
        let mut settings = Config::default();

        // 1. Default values
        settings.set_default("VIPER_BACKEND", "Silicon").unwrap();
        settings.set_default("CHECK_FOLDUNFOLD_STATE", false).unwrap();
        settings.set_default("CHECK_BINARY_OPERATIONS", false).unwrap();
        settings.set_default("CHECK_PANICS", true).unwrap();
        settings.set_default("ENCODE_UNSIGNED_NUM_CONSTRAINT", false).unwrap();
        settings.set_default("SIMPLIFY_ENCODING", true).unwrap();
        settings.set_default("LOG_DIR", "./log/").unwrap();
        settings.set_default("DUMP_DEBUG_INFO", false).unwrap();
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
        settings.set_default("REPORT_SUPPORT_STATUS", true).unwrap();
        settings.set_default("SKIP_UNSUPPORTED_FUNCTIONS", false).unwrap();
        settings.set_default("ERROR_ON_PARTIALLY_SUPPORTED", false).unwrap();
        settings.set_default("NO_VERIFY", false).unwrap();
        settings.set_default("FULL_COMPILATION", false).unwrap();
        settings.set_default("JSON_COMMUNICATION", false).unwrap();

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

        settings
    });
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
pub fn check_binary_operations() -> bool {
    read_setting("CHECK_BINARY_OPERATIONS")
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

/// Report the support status of functions using the compiler's error messages
pub fn report_support_status() -> bool {
    read_setting("REPORT_SUPPORT_STATUS")
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

/// Replace the given basic blocks with ``assume false``.
pub fn delete_basic_blocks() -> Vec<String> {
    read_setting("DELETE_BASIC_BLOCKS")
}

/// Skip functions that are unsupported or partially supported
pub fn skip_unsupported_functions() -> bool {
    read_setting("SKIP_UNSUPPORTED_FUNCTIONS")
}

/// Raise error messages even for partially supported language features.
/// Note: this overrides SKIP_UNSUPPORTED_FUNCTIONS
pub fn error_on_partially_supported() -> bool {
    read_setting("ERROR_ON_PARTIALLY_SUPPORTED")
}

/// Skip the verification
pub fn no_verify() -> bool {
    read_setting("NO_VERIFY")
}

/// Continue the compilation and generate the binary after Prusti terminates
pub fn full_compilation() -> bool {
    read_setting("FULL_COMPILATION")
}
