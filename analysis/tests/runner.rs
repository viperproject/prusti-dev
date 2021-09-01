#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]

/// Source: https://github.com/rust-lang/miri/blob/master/tests/compiletest.rs
use std::env;
use std::path::PathBuf;

use compiletest_rs as compiletest;

fn get_driver_path() -> PathBuf {
    let target_directory = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    let executable_name = if cfg!(windows) {
        "analysis-driver.exe"
    } else {
        "analysis-driver"
    };
    let local_driver_path: PathBuf = ["target", target_directory, executable_name]
        .iter()
        .collect();
    if local_driver_path.exists() {
        return local_driver_path;
    }
    let workspace_driver_path: PathBuf = ["..", "target", target_directory, executable_name]
        .iter()
        .collect();
    if workspace_driver_path.exists() {
        return workspace_driver_path;
    }
    panic!(
        "Could not find the {:?} {:?} binary to be used in tests. \
        It might be that the project has not been compiled correctly.",
        target_directory, executable_name
    );
}

fn find_sysroot() -> String {
    // Taken from https://github.com/Manishearth/rust-clippy/pull/911.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect("need to specify RUST_SYSROOT env var or use rustup or multirust")
            .to_owned(),
    }
}

fn run_tests(mode: &str, path: &str, custom_args: Vec<String>) {
    let mut config = compiletest::Config::default();
    let mut flags = Vec::new();
    flags.push("--edition 2018".to_owned());
    flags.push(format!("--sysroot {}", find_sysroot()));
    flags.extend(custom_args.into_iter());
    config.target_rustcflags = Some(flags.join(" "));
    config.mode = mode.parse().expect("Invalid mode");
    config.rustc_path = get_driver_path();
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
        vec!["--ADdomain=ReachingDefsState".into()],
    );
    run_tests(
        "ui",
        "tests/test_cases/definitely_initialized",
        vec!["--ADdomain=DefinitelyInitializedState".into()],
    );
}
