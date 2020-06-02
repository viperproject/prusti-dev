#![feature(nll)]

extern crate prusti_common;
extern crate walkdir;

use prusti_common::driver_utils;
use std::process::Command;
use std::str;

fn main() {
    if let Err(code) = process(std::env::args().skip(1).collect()) {
        std::process::exit(code);
    }
}

fn process(args: Vec<String>) -> Result<(), i32> {
    let mut prusti_driver_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("prusti-filter-driver");
    if cfg!(windows) {
        prusti_driver_path.set_extension("exe");
    }

    let prusti_sysroot =
        driver_utils::prusti_sysroot().expect(&format!("Failed to find Rust's sysroot for Prusti"));

    let compiler_lib = prusti_sysroot.join("lib");

    let prusti_home = prusti_driver_path
        .parent()
        .expect("Failed to find Prusti's home");

    let prusti_contracts_lib = driver_utils::find_prusti_contracts(&prusti_home)
        .expect("Failed to find prusti_contracts library in Prusti's home");

    let mut cmd = Command::new(&prusti_driver_path);
    cmd.args(args);
    cmd.env("SYSROOT", &prusti_sysroot);
    cmd.env("PRUSTI_CONTRACTS_LIB", &prusti_contracts_lib);

    let mut libs = vec![compiler_lib];
    if let Some(target) = option_env!("TARGET") {
        let rustlib_path = prusti_sysroot
            .join("lib")
            .join("rustlib")
            .join(target)
            .join("lib");
        libs.push(rustlib_path);
    }
    driver_utils::add_to_loader_path(libs, &mut cmd);

    let exit_status = cmd.status().expect("could not run prusti-filter-driver");

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
