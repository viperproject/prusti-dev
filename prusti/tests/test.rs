extern crate compiletest_rs;

use compiletest_rs::{common, run_tests, Config};
use std::env::{remove_var, set_var, var};
use std::path::PathBuf;

static PRUSTI_CONTRACTS_LIB: &'static str = "../target/debug/libprusti_contracts.rlib";

fn get_driver_path() -> PathBuf {
    let local_driver_path = if cfg!(windows) {
        PathBuf::from("target/debug/prusti-driver.exe")
    } else {
        PathBuf::from("target/debug/prusti-driver")
    };
    let workspace_driver_path = if cfg!(windows) {
        PathBuf::from("../target/debug/prusti-driver.exe")
    } else {
        PathBuf::from("../target/debug/prusti-driver")
    };
    if local_driver_path.exists() {
        return local_driver_path;
    }
    if workspace_driver_path.exists() {
        return workspace_driver_path;
    }
    panic!("Could not find the prusti-driver binary to be used in tests");
}

fn run_no_verification(group_name: &str) {
    set_var("PRUSTI_CONTRACTS_LIB", PRUSTI_CONTRACTS_LIB);
    set_var("PRUSTI_FULL_COMPILATION", "true");

    // This flag informs the driver that we are running the test suite, so that some additional
    // checks are enabled. For example, comparison of the computed definitely initialized
    // information with the expected one.
    set_var("PRUSTI_TEST", "true");

    set_var("PRUSTI_NO_VERIFY", "true");
    set_var("PRUSTI_QUIET", "true");

    let mut config = Config::default();
    config.rustc_path = get_driver_path();
    config.link_deps();

    // Filter the tests to run
    if let Ok(name) = var::<&str>("TESTNAME") {
        let s: String = name.to_owned();
        config.filter = Some(s)
    }

    let path = PathBuf::from(format!("tests/{}/ui", group_name));
    if path.exists() {
        config.mode = common::Mode::Ui;
        config.src_base = path;
        run_tests(&config);
    }

    let path = PathBuf::from(format!("tests/{}/pass", group_name));
    if path.exists() {
        config.mode = common::Mode::RunPass;
        config.src_base = path;
        run_tests(&config);
    }

    let path = PathBuf::from(format!("tests/{}/fail", group_name));
    if path.exists() {
        config.mode = common::Mode::CompileFail;
        config.src_base = path;
        run_tests(&config);
    }
}

fn run_verification(group_name: &str) {
    set_var("PRUSTI_CONTRACTS_LIB", PRUSTI_CONTRACTS_LIB);
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
    remove_var("PRUSTI_QUIET");

    let mut config = Config::default();
    config.rustc_path = get_driver_path();
    config.link_deps();

    // Disable warnings
    config.target_rustcflags = Some("-A warnings".to_string());

    // Filter the tests to run
    if let Ok(name) = var::<&str>("TESTNAME") {
        let s: String = name.to_owned();
        config.filter = Some(s)
    }

    let path = PathBuf::from(format!("tests/{}/ui", group_name));
    if path.exists() {
        config.mode = common::Mode::Ui;
        config.src_base = path;
        run_tests(&config);
    }

    let path = PathBuf::from(format!("tests/{}/pass", group_name));
    if path.exists() {
        config.mode = common::Mode::RunPass;
        config.src_base = path;
        run_tests(&config);
    }

    let path = PathBuf::from(format!("tests/{}/pass-overflow", group_name));
    if path.exists() {
        config.mode = common::Mode::RunPass;
        config.src_base = path;
        set_var("PRUSTI_CHECK_BINARY_OPERATIONS", "true");
        run_tests(&config);
        set_var("PRUSTI_CHECK_BINARY_OPERATIONS", "false");
    }

    let path = PathBuf::from(format!("tests/{}/fail", group_name));
    if path.exists() {
        config.mode = common::Mode::CompileFail;
        config.src_base = path;
        run_tests(&config);
    }

    let path = PathBuf::from(format!("tests/{}/fail-overflow", group_name));
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
    run_no_verification("parse");
    run_no_verification("typecheck");
    run_verification("verify");
}
