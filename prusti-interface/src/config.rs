// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use config_crate::{Config, Environment, File};
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
        settings.set_default("DUMP_BRANCH_CTXT_IN_DEBUG_INFO", false).unwrap();
        settings.set_default("DUMP_REBORROWING_DAG_IN_DEBUG_INFO", false).unwrap();
        settings.set_default("DUMP_BORROWCK_INFO", false).unwrap();
        settings.set_default("DUMP_VIPER_PROGRAM", false).unwrap();
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

/// Generate additional, *slow*, checks for the foldunfold algorithm
pub fn check_foldunfold_state() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("CHECK_FOLDUNFOLD_STATE")
        .unwrap()
}

/// The Viper backend that should be used for the verification
pub fn viper_backend() -> String {
    SETTINGS
        .read()
        .unwrap()
        .get::<String>("VIPER_BACKEND")
        .unwrap()
        .to_lowercase()
        .trim()
        .to_string()
}

/// Should we check absence of panics?
pub fn check_panics() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("CHECK_PANICS")
        .unwrap()
}

/// Should we simplify the encoding before passing it to Viper?
pub fn simplify_encoding() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("SIMPLIFY_ENCODING")
        .unwrap()
}

/// Whether to use the verifiation whitelist
pub fn enable_whitelist() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("ENABLE_WHITELIST")
        .unwrap()
}

/// Get the whitelist of procedures that should be verified
pub fn verification_whitelist() -> Vec<String> {
    SETTINGS
        .read()
        .unwrap()
        .get::<Vec<String>>("WHITELIST")
        .unwrap()
}

/// Should we dump debug files?
pub fn dump_debug_info() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("DUMP_DEBUG_INFO")
        .unwrap()
}

/// Should we dump the branch context state in debug files?
pub fn dump_branch_ctxt_in_debug_info() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("DUMP_BRANCH_CTXT_IN_DEBUG_INFO")
        .unwrap()
}

/// Should we dump the reborrowing DAGs in debug files?
pub fn dump_reborrowing_dag_in_debug_info() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("DUMP_REBORROWING_DAG_IN_DEBUG_INFO")
        .unwrap()
}

/// Should we dump borrowck info?
pub fn dump_borrowck_info() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("DUMP_BORROWCK_INFO")
        .unwrap()
}

/// Should we dump the Viper program?
pub fn dump_viper_program() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("DUMP_VIPER_PROGRAM")
        .unwrap()
}

/// How many parent folders should be used to disambiguate the Viper dumps (and other debug files)?
pub fn num_parents_for_dumps() -> u64 {
    SETTINGS
        .read()
        .unwrap()
        .get::<u64>("NUM_PARENTS_FOR_DUMPS")
        .unwrap()
}

/// In which folder should we sore log/dumps?
pub fn log_dir() -> String {
    SETTINGS.read().unwrap().get::<String>("LOG_DIR").unwrap()
}

/// Check binary operations for overflows
pub fn check_binary_operations() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("CHECK_BINARY_OPERATIONS")
        .unwrap()
}

/// Encode (and check) that unsigned integers are non-negative.
pub fn encode_unsigned_num_constraint() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("ENCODE_UNSIGNED_NUM_CONSTRAINT")
        .unwrap()
}

/// Location of 'libprusti_contracts*.rlib'
pub fn contracts_lib() -> String {
    SETTINGS
        .read()
        .unwrap()
        .get::<String>("CONTRACTS_LIB")
        .unwrap()
}

/// Get extra JVM arguments
pub fn extra_jvm_args() -> Vec<String> {
    SETTINGS
        .read()
        .unwrap()
        .get::<Vec<String>>("EXTRA_JVM_ARGS")
        .unwrap()
}

/// Get extra arguments for the verifier
pub fn extra_verifier_args() -> Vec<String> {
    SETTINGS
        .read()
        .unwrap()
        .get::<Vec<String>>("EXTRA_VERIFIER_ARGS")
        .unwrap()
}

/// Should we hide user messages?
pub fn quiet() -> bool {
    SETTINGS.read().unwrap().get::<bool>("QUIET").unwrap()
}

/// The assert timeout (in miliseconds) passed to Silicon.
pub fn assert_timeout() -> u64 {
    SETTINGS
        .read()
        .unwrap()
        .get::<u64>("ASSERT_TIMEOUT")
        .unwrap()
}

/// Use the Silicon configuration option `--enableMoreCompleteExhale`.
pub fn use_more_complete_exhale() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("USE_MORE_COMPLETE_EXHALE")
        .unwrap()
}

/// Report the support status of functions using the compiler's error messages
pub fn report_support_status() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("REPORT_SUPPORT_STATUS")
        .unwrap()
}

/// Disable mangling of generated Viper names.
///
/// **Note:** This is very likely to result in invalid programs being
/// generated because of name collisions.
pub fn disable_name_mangling() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("DISABLE_NAME_MANGLING")
        .unwrap()
}

/// Verify only the preamble: domains, functions, and predicates.
///
/// **Note:** With this flag enabled, no methods are verified!
pub fn verify_only_preamble() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("VERIFY_ONLY_PREAMBLE")
        .unwrap()
}

/// Verify only the path given in ``VERIFY_ONLY_BASIC_BLOCK_PATH``.
///
/// **Note:** This flag is only for debugging Prusti!
pub fn enable_verify_only_basic_block_path() -> bool {
    SETTINGS
        .read()
        .unwrap()
        .get::<bool>("ENABLE_VERIFY_ONLY_BASIC_BLOCK_PATH")
        .unwrap()
}

/// Verify only the single execution path goes through the given basic blocks.
///
/// All basic blocks not on this execution path are replaced with
/// ``assume false``.
///
/// **Note:** This flag is only for debugging Prusti!
pub fn verify_only_basic_block_path() -> Vec<String> {
    SETTINGS
        .read()
        .unwrap()
        .get::<Vec<String>>("VERIFY_ONLY_BASIC_BLOCK_PATH")
        .unwrap()
}

/// Replace the given basic blocks with ``assume false``.
pub fn delete_basic_blocks() -> Vec<String> {
    SETTINGS
        .read()
        .unwrap()
        .get::<Vec<String>>("DELETE_BASIC_BLOCKS")
        .unwrap()
}
