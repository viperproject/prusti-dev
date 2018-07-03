extern crate compiletest_rs;

use std::env::{set_var, remove_var};
use std::path::PathBuf;
use compiletest_rs::{common, run_tests, Config};

static RUSTC_FLAGS: &'static str = "-Z mir-emit-validate=1 -Z borrowck=mir";
static LOCAL_DRIVER_PATH: &'static str = "target/debug/prusti-driver";
static WORKSPACE_DRIVER_PATH: &'static str = "../target/debug/prusti-driver";
static WORKSPACE_PRUSTI_CONTRACTS_PATH: &'static str = "../target/debug/libprusti_contracts.rlib";

fn get_driver_path() -> PathBuf {
    if PathBuf::from(LOCAL_DRIVER_PATH).exists() {
        return PathBuf::from(LOCAL_DRIVER_PATH);
    }
    if PathBuf::from(WORKSPACE_DRIVER_PATH).exists() {
        return PathBuf::from(WORKSPACE_DRIVER_PATH);
    }
    unreachable!();
}

fn run(group_name: &str, verify: bool) {
    set_var("PRUSTI_FULL_COMPILATION", "true");

    if !verify {
        set_var("PRUSTI_NO_VERIFY", "true");
    } else {
        remove_var("PRUSTI_NO_VERIFY");
    }

    let mut config = Config::default();
    config.rustc_path = get_driver_path();
    let mut rustc_flags = RUSTC_FLAGS.to_string();
    if PathBuf::from(WORKSPACE_PRUSTI_CONTRACTS_PATH).exists() {
        rustc_flags.push_str(" --extern prusti_contracts=");
        rustc_flags.push_str(WORKSPACE_PRUSTI_CONTRACTS_PATH);
    }
    config.target_rustcflags = Some(rustc_flags);
    config.link_deps();

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

#[test]
fn typecheck_test() {
    run("parse", false);
    run("typecheck", false);
    run("verify", true);
}
