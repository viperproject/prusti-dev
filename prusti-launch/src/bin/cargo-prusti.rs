// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_launch::get_rust_toolchain_channel;
use std::process::Command;

fn main() {
    if let Err(code) = process(std::env::args().skip(1)) {
        std::process::exit(code);
    }
}

fn process<I>(args: I) -> Result<(), i32>
where
    I: Iterator<Item = String>,
{
    let mut prusti_rustc_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("prusti-rustc");
    if cfg!(windows) {
        prusti_rustc_path.set_extension("exe");
    }

    // Remove the leading "prusti" argument when `cargo-prusti` is invocated
    // as `cargo prusti` (note the space)
    let clean_args = args.skip_while(|x| x == "prusti");

    let cargo_path = std::env::var("CARGO_PATH").unwrap_or_else(|_| "cargo".to_string());
    let original_cargo_target =
        std::env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string());
    let cargo_target = format!("{}/verify", original_cargo_target);
    let prusti_log_dir =
        std::env::var("PRUSTI_LOG_DIR").unwrap_or_else(|_| format!("{}/log", cargo_target));

    let exit_status = Command::new(cargo_path)
        .arg("check")
        .args(clean_args)
        .env("RUST_TOOLCHAIN", get_rust_toolchain_channel())
        .env("RUSTC_WRAPPER", prusti_rustc_path)
        .env("CARGO_TARGET_DIR", cargo_target)
        .env("PRUSTI_QUIET", "true")
        .env("PRUSTI_FULL_COMPILATION", "true")
        .env("PRUSTI_LOG_DIR", prusti_log_dir)
        .status()
        .expect("could not run cargo");

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
