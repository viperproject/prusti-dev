#![feature(custom_test_frameworks)]
// Custom test runner, to avoid libtest being wrapped around compiletest which
// wraps libtest.
#![test_runner(test_runner)]

use compiletest_rs as compiletest;
use std::env::{self, set_var};
use std::path::PathBuf;
use prusti_server::ServerSideService;

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

fn run_tests(mode: &str, path: &str) {
    // Ask prusti-rustc to load all proc-macro crates for us.
    set_var("PRUSTI_LOAD_ALL_PROC_MACRO_CRATES", "true");

    // Add some flags we always want.
    let mut flags = Vec::new();
    flags.push("--edition 2018".to_owned());

    let flags = flags.join(" ");
    eprintln!("   Compiler flags: {}", flags);

    // The rest of the configuration.
    let mut config = compiletest::Config::default();
    config.mode = mode.parse().expect("Invalid mode");
    config.rustc_path = get_prusti_rustc_path();
    if let Some(lib_path) = option_env!("RUSTC_LIB_PATH") {
        config.run_lib_path = PathBuf::from(lib_path);
        config.compile_lib_path = PathBuf::from(lib_path);
    }
    config.filter = env::args().nth(1);
    config.src_base = PathBuf::from(path);
    config.target_rustcflags = Some(flags);
    compiletest::run_tests(&config);
}

fn test_runner(_tests: &[&()]) {
    // spawn server process as child (so it stays around until main function terminates)
    let server_address = ServerSideService::spawn_off_thread();
    set_var("PRUSTI_SERVER_ADDRESS", server_address.to_string());

    run_tests("ui", "tests/pass/parse");
    run_tests("ui", "tests/pass/typecheck");

    set_var("PRUSTI_QUIET", "true");
    //run_tests("ui", "tests/verify/pass");
    //run_tests("compile-fail", "tests/verify/fail");
}
