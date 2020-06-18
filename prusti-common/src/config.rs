// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use config_crate::{Config, Environment, File};
use serde::Deserialize;
use std::env;
use std::sync::RwLock;

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
        settings.set_default("ENABLE_WHITELIST", false).unwrap();
        settings.set_default::<Vec<String>>("WHITELIST", vec![]).unwrap();
        settings.set_default("LOG_DIR", "./log/").unwrap();
        settings.set_default("DUMP_DEBUG_INFO", false).unwrap();
        settings.set_default("DUMP_PATH_CTXT_IN_DEBUG_INFO", false).unwrap();
        settings.set_default("DUMP_REBORROWING_DAG_IN_DEBUG_INFO", false).unwrap();
        settings.set_default("DUMP_BORROWCK_INFO", false).unwrap();
        settings.set_default("DUMP_VIPER_PROGRAM", false).unwrap();
        settings.set_default("FOLDUNFOLD_STATE_FILTER", "").unwrap();
        settings.set_default("NUM_PARENTS_FOR_DUMPS", 0).unwrap();
        settings.set_default("CONTRACTS_LIB", "").unwrap();
        settings.set_default::<Vec<String>>("EXTRA_JVM_ARGS", vec![]).unwrap();
        settings.set_default::<Vec<String>>("EXTRA_VERIFIER_ARGS", vec![]).unwrap();
        settings.set_default("QUIET", false).unwrap();
        settings.set_default("ASSERT_TIMEOUT", 10_000).unwrap();
        settings.set_default("USE_MORE_COMPLETE_EXHALE", true).unwrap();
        settings.set_default("REPORT_SUPPORT_STATUS", true).unwrap();

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

fn read_setting<T>(name: &'static str) -> T
where
    T: Deserialize<'static>,
{
    SETTINGS.read().unwrap().get(name).unwrap()
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

/// Whether to use the verifiation whitelist
pub fn enable_whitelist() -> bool {
    read_setting("ENABLE_WHITELIST")
}

/// Get the whitelist of procedures that should be verified
pub fn verification_whitelist() -> Vec<String> {
    read_setting("WHITELIST")
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

/// How many parent folders should be used to disambiguate the Viper dumps (and other debug files)?
pub fn num_parents_for_dumps() -> u64 {
    read_setting("NUM_PARENTS_FOR_DUMPS")
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
