#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]

mod utils;

/// Source: https://github.com/rust-lang/miri/blob/master/tests/compiletest.rs
use compiletest_rs as compiletest;
use std::{env, path::PathBuf};
use utils::*;

fn run_tests(mode: &str, path: &str, custom_args: Vec<String>) {
    let mut config = compiletest::Config::default();
    let mut flags = Vec::new();
    flags.push("--edition 2018".to_owned());
    flags.push(format!("--sysroot {}", find_sysroot()));
    flags.extend(custom_args.into_iter());
    config.target_rustcflags = Some(flags.join(" "));
    config.mode = mode.parse().expect("Invalid mode");
    config.rustc_path = find_compiled_executable("analysis-driver");
    config.src_base = PathBuf::from(path);
    if let Some(lib_path) = option_env!("RUSTC_LIB_PATH") {
        config.run_lib_path = PathBuf::from(lib_path);
        config.compile_lib_path = PathBuf::from(lib_path);
    }
    compiletest::run_tests(&config);
}

fn test_runner(_tests: &[&()]) {
    env::set_var("RUST_BACKTRACE", "1");

    run_tests(
        "ui",
        "tests/test_cases/reaching_definitions",
        vec!["--analysis=ReachingDefsAnalysis".into()],
    );
    run_tests(
        "ui",
        "tests/test_cases/definitely_initialized",
        vec!["--analysis=DefinitelyInitializedAnalysis".into()],
    );
    run_tests(
        "ui",
        "tests/test_cases/relaxed_definitely_initialized",
        vec!["--analysis=RelaxedDefinitelyInitializedAnalysis".into()],
    );
    run_tests(
        "ui",
        "tests/test_cases/maybe_borrowed",
        vec!["--analysis=MaybeBorrowedAnalysis".into()],
    );
    run_tests(
        "ui",
        "tests/test_cases/definitely_accessible",
        vec!["--analysis=DefinitelyAccessibleAnalysis".into()],
    );
}
