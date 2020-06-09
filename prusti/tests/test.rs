extern crate compiletest_rs;

use compiletest_rs::{common, run_tests, Config};
use std::env::{remove_var, set_var, var};
use std::path::PathBuf;

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

fn run_no_verification(group_name: &str) {
    set_var("PRUSTI_FULL_COMPILATION", "true");

    // This flag informs the driver that we are running the test suite, so that some additional
    // checks are enabled. For example, comparison of the computed definitely initialized
    // information with the expected one.
    set_var("PRUSTI_TEST", "true");

    set_var("PRUSTI_NO_VERIFY", "true");
    set_var("PRUSTI_QUIET", "true");

    let mut config = Config::default();
    config.rustc_path = get_prusti_rustc_path();

    // Filter the tests to run
    if let Ok(name) = var::<&str>("TESTNAME") {
        let s: String = name.to_owned();
        config.filter = Some(s)
    }

    let path: PathBuf = ["tests", group_name, "ui"].iter().collect();
    if path.exists() {
        config.target_rustcflags = Some("--color=never".to_string());
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

fn run_verification(group_name: &str) {
    set_var("PRUSTI_FULL_COMPILATION", "true");

    // This flag informs the driver that we are running the test suite, so that some additional
    // checks are enabled. For example, comparison of the computed definitely initialized
    // information with the expected one.
    set_var("PRUSTI_TEST", "true");

    set_var("PRUSTI_CHECK_BINARY_OPERATIONS", "false");
    set_var("PRUSTI_DUMP_DEBUG_INFO", "false");
    set_var("PRUSTI_DUMP_BORROWCK_INFO", "false");
    set_var("PRUSTI_ENCODE_UNSIGNED_NUM_CONSTRAINT", "true");
    set_var("PRUSTI_REPORT_SUPPORT_STATUS", "false");

    remove_var("PRUSTI_NO_VERIFY");
    set_var("PRUSTI_QUIET", "true");

    let mut config = Config::default();
    config.rustc_path = get_prusti_rustc_path();

    // Disable warnings
    config.target_rustcflags = Some("-A warnings".to_string());

    // Filter the tests to run
    if let Ok(name) = var::<&str>("TESTNAME") {
        let s: String = name.to_owned();
        config.filter = Some(s)
    }

    let path: PathBuf = ["tests", group_name, "ui"].iter().collect();
    if path.exists() {
        config.target_rustcflags = Some("--color=never".to_string());
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

    let path: PathBuf = ["tests", group_name, "pass-overflow"].iter().collect();
    if path.exists() {
        config.mode = common::Mode::RunPass;
        config.src_base = path;
        set_var("PRUSTI_CHECK_BINARY_OPERATIONS", "true");
        run_tests(&config);
        set_var("PRUSTI_CHECK_BINARY_OPERATIONS", "false");
    }

    let path: PathBuf = ["tests", group_name, "fail"].iter().collect();
    if path.exists() {
        config.mode = common::Mode::CompileFail;
        config.src_base = path;
        run_tests(&config);
    }

    let path: PathBuf = ["tests", group_name, "fail-overflow"].iter().collect();
    if path.exists() {
        config.mode = common::Mode::CompileFail;
        config.src_base = path;
        set_var("PRUSTI_CHECK_BINARY_OPERATIONS", "true");
        run_tests(&config);
        set_var("PRUSTI_CHECK_BINARY_OPERATIONS", "false");
    }
}

#[test]
fn test_runner() {
    // TODO: spawn server process as child (so it stays around until main function terminates)
    run_no_verification("parse");
    run_no_verification("typecheck");
    run_verification("verify");
}
