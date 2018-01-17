extern crate compiletest_rs;

use std::env::set_var;
use std::path::PathBuf;
use compiletest_rs::{Config, common, run_tests};

static RUSTC_FLAGS: &'static str = "-Z mir-emit-validate=1 -Z borrowck=mir -Z nll";

fn run(group_name: &str) {
    set_var("PRUSTI_TESTS", "true");

    let mut config = Config::default();
    config.rustc_path = PathBuf::from("target/debug/prusti-driver");
    config.target_rustcflags = Some(RUSTC_FLAGS.to_string());
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
    run("parse");
    run("typecheck");
}
