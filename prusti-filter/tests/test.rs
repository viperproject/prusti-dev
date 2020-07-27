#![allow(dead_code)]

extern crate compiletest_rs;

use compiletest_rs::{common, run_tests, Config};
use std::env::var;
use std::path::PathBuf;

fn get_prusti_filter_path() -> PathBuf {
    let local_prusti_filter_path: PathBuf = if cfg!(windows) {
        ["target", "debug", "prusti-filter.exe"].iter().collect()
    } else {
        ["target", "debug", "prusti-filter"].iter().collect()
    };
    let workspace_prusti_filter_path: PathBuf = if cfg!(windows) {
        ["..", "target", "debug", "prusti-filter.exe"].iter().collect()
    } else {
        ["..", "target", "debug", "prusti-filter"].iter().collect()
    };
    if local_prusti_filter_path.exists() {
        return local_prusti_filter_path;
    }
    if workspace_prusti_filter_path.exists() {
        return workspace_prusti_filter_path;
    }
    panic!("Could not find the prusti-filter binary to be used in tests");
}

fn run_filter(group_name: &str) {
    let mut config = Config::default();
    config.rustc_path = get_prusti_filter_path();

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
    //run_filter("filter"); FIXME
}
