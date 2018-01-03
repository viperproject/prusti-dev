extern crate compiletest_rs;

use std::path::PathBuf;
use compiletest_rs::{Config, common, run_tests};

static RUSTC_FLAGS: &'static str = "-Z mir-emit-validate=1 -Z extra-plugins=prusti -Z borrowck=mir -Z nll";

fn run(group_name: &str) {
    let mut config = Config::default();
    config.target_rustcflags = Some(RUSTC_FLAGS.to_string());
    config.link_deps();

    config.mode = common::Mode::RunPass;
    config.src_base = PathBuf::from(format!("tests/{}/pass", group_name));
    run_tests(&config);

    config.mode = common::Mode::CompileFail;
    config.src_base = PathBuf::from(format!("tests/{}/fail", group_name));
    run_tests(&config);
}

#[test]
fn typecheck_test() {
    run("typecheck");
}
