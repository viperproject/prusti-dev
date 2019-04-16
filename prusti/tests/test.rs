extern crate compiletest_rs;

use std::env::{var, set_var, remove_var};
use std::path::PathBuf;
use compiletest_rs::{common, run_tests, Config};

static LOCAL_DRIVER_PATH: &'static str = "target/debug/prusti-driver";
static WORKSPACE_DRIVER_PATH: &'static str = "../target/debug/prusti-driver";
static PRUSTI_CONTRACTS_LIB: &'static str = "../target/debug/libprusti_contracts.rlib";

fn get_driver_path() -> PathBuf {
    if PathBuf::from(LOCAL_DRIVER_PATH).exists() {
        return PathBuf::from(LOCAL_DRIVER_PATH);
    }
    if PathBuf::from(WORKSPACE_DRIVER_PATH).exists() {
        return PathBuf::from(WORKSPACE_DRIVER_PATH);
    }
    unreachable!();
}

fn run_no_verification(group_name: &str) {
    set_var("PRUSTI_CONTRACTS_LIB", PRUSTI_CONTRACTS_LIB);
    set_var("PRUSTI_FULL_COMPILATION", "true");

    // This flag informs the driver that we are running the test suite, so that some additional
    // checks are enabled. For example, comparison of the computed definitely initialized
    // information with the expected one.
    set_var("PRUSTI_TEST", "true");

    set_var("PRUSTI_NO_VERIFY", "true");

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

    remove_var("PRUSTI_NO_VERIFY");

    let mut config = Config::default();
    config.rustc_path = get_driver_path();
    config.link_deps();

    // Disable warnings
    config.target_rustcflags = Some("-A warnings");

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
