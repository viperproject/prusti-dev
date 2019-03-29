// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::sync::RwLock;
use std::env;
use config_crate::{Config, Environment, File};

lazy_static! {
    // Is this RwLock<..> necessary?
    static ref SETTINGS: RwLock<Config> = RwLock::new({
        let mut settings = Config::default();

        // 1. Default values
        settings.set_default("VIPER_BACKEND", "Silicon").unwrap();
        settings.set_default("CHECK_FOLDUNFOLD_STATE", false).unwrap();
        settings.set_default("CHECK_BINARY_OPERATIONS", false).unwrap();
        settings.set_default("CHECK_PANICS", true).unwrap();
        settings.set_default("SIMPLIFY_EXPRESSIONS", true).unwrap();
        settings.set_default("CHECK_UNREACHABLE_TERMINATORS", false).unwrap();
        settings.set_default("ENABLE_WHITELIST", false).unwrap();
        settings.set_default::<Vec<String>>("WHITELIST", vec![]).unwrap();
        settings.set_default("LOG_DIR", "./log/").unwrap();
        settings.set_default("DUMP_DEBUG_INFO", false).unwrap();
        settings.set_default("DUMP_BORROWCK_INFO", false).unwrap();
        settings.set_default("CONTRACTS_LIB", "").unwrap();
        settings.set_default::<Vec<String>>("EXTRA_JVM_ARGS", vec![]).unwrap();
        settings.set_default::<Vec<String>>("EXTRA_VERIFIER_ARGS", vec![]).unwrap();
        settings.set_default("SIMPLIFY_FUNCTIONS", true).unwrap();
        settings.set_default("QUIET", false).unwrap();
        settings.set_default("ASSERT_TIMEOUT", 1000).unwrap();

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
    SETTINGS.read().unwrap().get::<bool>("CHECK_FOLDUNFOLD_STATE").unwrap()
}

/// The Viper backend that should be used for the verification
pub fn viper_backend() -> String {
    SETTINGS.read().unwrap().get::<String>("VIPER_BACKEND").unwrap().to_lowercase().trim().to_string()
}

/// Should we check absence of panics?
pub fn check_panics() -> bool {
    SETTINGS.read().unwrap().get::<bool>("CHECK_PANICS").unwrap()
}

/// Should we simplify expressions?
pub fn simplify_expressions() -> bool {
    SETTINGS.read().unwrap().get::<bool>("SIMPLIFY_EXPRESSIONS").unwrap()
}

/// Should we check that "Unreachable" terminators are actually unreachable?
/// It should be guaranteed by the compiler.
pub fn check_unreachable_terminators() -> bool {
    SETTINGS.read().unwrap().get::<bool>("CHECK_UNREACHABLE_TERMINATORS").unwrap()
}

/// Whether to use the verifiation whitelist
pub fn enable_whitelist() -> bool {
    SETTINGS.read().unwrap().get::<bool>("ENABLE_WHITELIST").unwrap()
}

/// Get the whitelist of procedures that should be verified
pub fn verification_whitelist() -> Vec<String> {
    SETTINGS.read().unwrap().get::<Vec<String>>("WHITELIST").unwrap()
}

/// Should we dump debug files?
pub fn dump_debug_info() -> bool {
    SETTINGS.read().unwrap().get::<bool>("DUMP_DEBUG_INFO").unwrap()
}

/// Should we dump borrowck info?
pub fn dump_borrowck_info() -> bool {
    SETTINGS.read().unwrap().get::<bool>("DUMP_BORROWCK_INFO").unwrap()
}

/// In which folder should we sore log/dumps?
pub fn log_dir() -> String {
    SETTINGS.read().unwrap().get::<String>("LOG_DIR").unwrap()
}

/// Check binary operations for overflows
pub fn check_binary_operations() -> bool {
    SETTINGS.read().unwrap().get::<bool>("CHECK_BINARY_OPERATIONS").unwrap()
}

/// Location of 'libprusti_contracts*.rlib'
pub fn contracts_lib() -> String {
    SETTINGS.read().unwrap().get::<String>("CONTRACTS_LIB").unwrap()
}

/// Get extra JVM arguments
pub fn extra_jvm_args() -> Vec<String> {
    SETTINGS.read().unwrap().get::<Vec<String>>("EXTRA_JVM_ARGS").unwrap()
}

/// Get extra arguments for the verifier
pub fn extra_verifier_args() -> Vec<String> {
    SETTINGS.read().unwrap().get::<Vec<String>>("EXTRA_VERIFIER_ARGS").unwrap()
}

/// Should we simplify functions?
pub fn simplify_functions() -> bool {
    SETTINGS.read().unwrap().get::<bool>("SIMPLIFY_FUNCTIONS").unwrap()
}

/// Should we hide user messages?
pub fn quiet() -> bool {
    SETTINGS.read().unwrap().get::<bool>("QUIET").unwrap()
}

/// The assert timeout (in miliseonds) passed to Silicon.
pub fn assert_timeout() -> u64 {
    SETTINGS.read().unwrap().get::<u64>("ASSERT_TIMEOUT").unwrap()
}
