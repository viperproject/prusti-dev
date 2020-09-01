#![feature(custom_test_frameworks)]
// Custom test runner, to avoid libtest being wrapped around compiletest which
// wraps libtest.
#![test_runner(test_runner)]

extern crate compiletest_rs;
extern crate prusti_server;

use compiletest_rs::{common, run_tests, Config};
use prusti_server::ServerSideService;
use std::{env, path::PathBuf};

fn get_prusti_rustc_path() -> PathBuf {
    let local_prusti_rustc_path: PathBuf = if cfg!(windows) {
        ["target", "debug", "prusti-rustc.exe"].iter().collect()
    } else {
        ["target", "debug", "prusti-rustc"].iter().collect()
    };
    let workspace_prusti_rustc_path: PathBuf = if cfg!(windows) {
        ["..", "target", "debug", "prusti-rustc.exe"]
            .iter()
            .collect()
    } else {
        ["..", "target", "debug", "prusti-rustc"].iter().collect()
    };
    if local_prusti_rustc_path.exists() {
        return local_prusti_rustc_path;
    }
    if workspace_prusti_rustc_path.exists() {
        return workspace_prusti_rustc_path;
    }
    panic!("Could not find the prusti-rustc binary to be used in tests");
}

/// Set an environment variable, automatically reverting the change at the end of the lexical scope
struct TemporaryEnvVar {
    name: String,
    original: Option<String>,
}

impl TemporaryEnvVar {
    fn set(name: &str, value: &str) -> Self {
        let original: Option<String> = env::var(name).ok();
        env::set_var(name, value);
        TemporaryEnvVar {
            name: name.to_string(),
            original,
        }
    }
}

impl Drop for TemporaryEnvVar {
    fn drop(&mut self) {
        match self.original {
            Some(ref old_value) => env::set_var(&self.name, old_value),
            None => env::remove_var(&self.name),
        }
    }
}

fn run_prusti_tests(group_name: &str, filter: &Option<String>, rustc_flags: Option<&str>) {
    let mut config = Config::default();
    config.rustc_path = get_prusti_rustc_path();

    // Filter the tests to run
    config.filter = filter.clone();

    // Add compilation flags
    config.target_rustcflags = rustc_flags.map(|s| s.to_string());

    let path: PathBuf = ["tests", group_name, "ui"].iter().collect();
    if path.exists() {
        config.target_rustcflags = Some(format!(
            "{} --color=never",
            config.target_rustcflags.unwrap_or("".to_string())
        ));
        config.mode = common::Mode::Ui;
        config.src_base = path;
        run_tests(&config);
    }

    let path: PathBuf = ["tests", group_name, "pass"].iter().collect();
    if path.exists() {
        config.mode = common::Mode::RunPass;
        config.src_base = path;
        run_tests(&config);
    }

    let path: PathBuf = ["tests", group_name, "fail"].iter().collect();
    if path.exists() {
        config.mode = common::Mode::CompileFail;
        config.src_base = path;
        run_tests(&config);
    }
}

fn run_no_verification(group_name: &str, filter: &Option<String>) {
    // Automatically restored to their original value at the end of the lexical scope
    let _temporary_env_vars = (
        TemporaryEnvVar::set("PRUSTI_FULL_COMPILATION", "true"),
        TemporaryEnvVar::set("PRUSTI_NO_VERIFY", "true"),
        TemporaryEnvVar::set("PRUSTI_QUIET", "true"),
    );

    run_prusti_tests(group_name, filter, None);
}

fn run_filter(group_name: &str, filter: &Option<String>) {
    // Automatically restored to their original value at the end of the lexical scope
    let _temporary_env_vars = (
        TemporaryEnvVar::set("PRUSTI_FULL_COMPILATION", "true"),
        TemporaryEnvVar::set("PRUSTI_REPORT_SUPPORT_STATUS", "true"),
        TemporaryEnvVar::set("PRUSTI_ERROR_ON_PARTIALLY_SUPPORTED", "true"),
        TemporaryEnvVar::set("PRUSTI_SKIP_UNSUPPORTED_FUNCTIONS", "true"),
        TemporaryEnvVar::set("PRUSTI_QUIET", "true"),
    );

    run_prusti_tests(group_name, filter, Some("-A warnings"));
}

fn run_verification(group_name: &str, filter: &Option<String>) {
    // Automatically restored to their original value at the end of the lexical scope
    let _temporary_env_vars = (
        TemporaryEnvVar::set("PRUSTI_FULL_COMPILATION", "true"),
        TemporaryEnvVar::set("PRUSTI_DUMP_BORROWCK_INFO", "false"),
        TemporaryEnvVar::set("PRUSTI_ENCODE_UNSIGNED_NUM_CONSTRAINT", "true"),
        TemporaryEnvVar::set("PRUSTI_REPORT_SUPPORT_STATUS", "false"),
        TemporaryEnvVar::set("PRUSTI_QUIET", "true"),
    );

    run_prusti_tests(group_name, filter, Some("-A warnings"));
}

fn run_verification_overflow(group_name: &str, filter: &Option<String>) {
    // Automatically restored to their original value at the end of the lexical scope
    let _temporary_env_vars = (
        TemporaryEnvVar::set("PRUSTI_CHECK_BINARY_OPERATIONS", "true"),
    );

    run_verification(group_name, filter);
}

fn run_verification_core_proof(group_name: &str, filter: &Option<String>) {
    // Automatically restored to their original value at the end of the lexical scope
    let _temporary_env_vars = (
        TemporaryEnvVar::set("PRUSTI_CHECK_PANICS", "false"),
    );

    run_verification(group_name, filter);
}

fn test_runner(_tests: &[&()]) {
    // spawn server process as child (so it stays around until main function terminates)
    let server_address = ServerSideService::spawn_off_thread();
    env::set_var("PRUSTI_SERVER_ADDRESS", server_address.to_string());

    // Filter the tests to run
    let filter = env::args().nth(1);

    // Test the parsing of specifications. Doesn't run the verifier.
    println!("[parse]");
    run_no_verification("parse", &filter);

    // Test the type-checking of specifications. Doesn't run the verifier.
    println!("[typecheck]");
    run_no_verification("typecheck", &filter);

    // Test the error messages of prusti-filter
    println!("[filter]");
    run_filter("filter", &filter);

    // Test the verifier.
    println!("[verify]");
    run_verification("verify", &filter);

    // Test the verifier with overflow checks enabled.
    println!("[verify_overflow]");
    run_verification_overflow("verify_overflow", &filter);

    // Test the verifier with panic checks disabled (i.e. verify only the core proof).
    println!("[core_proof]");
    run_verification_core_proof("core_proof", &filter);
}
