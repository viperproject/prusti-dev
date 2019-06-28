extern crate compiletest_rs;

use compiletest_rs::{common, run_tests, Config};
use std::env::{remove_var, set_var, var};
use std::path::PathBuf;

static LOCAL_DRIVER_PATH: &'static str = "target/debug/prusti-filter";
static WORKSPACE_DRIVER_PATH: &'static str = "../target/debug/prusti-filter";
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

fn run_verification(group_name: &str) {
    set_var("PRUSTI_CONTRACTS_LIB", PRUSTI_CONTRACTS_LIB);

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

#[test]
fn test_runner() {
    run_verification("filter");
}
