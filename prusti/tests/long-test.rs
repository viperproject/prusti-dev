extern crate compiletest_rs;
extern crate prusti;
extern crate prusti_interface;

use std::env::{set_var, remove_var};
use std::path::PathBuf;
use compiletest_rs::{common, run_tests, Config};
use prusti::prusti_runner::run_prusti;
use prusti::driver_utils::silent_run;
use std::fs;
use prusti_interface::sysroot::current_sysroot;

static PRUSTI_CONTRACTS_LIB: &'static str = "../target/debug/libprusti_contracts.rlib";

// This test is disabled. Consider making a binary in src/ out of it.
//#[test]
fn test_runner() {
    set_var("PRUSTI_CONTRACTS_LIB", PRUSTI_CONTRACTS_LIB);
    let test_files = fs::read_dir("./tests/verify/long-pass").unwrap();
    for file in test_files.filter_map(Result::ok).filter(|f| f.path().extension().unwrap() == "rs") {
        let path = file.path().to_str().unwrap().to_string();
        println!("Testing '{}'...", path);
        let sys_root = current_sysroot().expect("need to specify SYSROOT");
        let exit_status = silent_run(move || {
            run_prusti(vec![
                "prusti".to_string(),
                "--sysroot".to_string(),
                sys_root,
                path
            ])
        });
        assert_eq!(0, exit_status);
    }
}
