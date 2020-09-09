// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::process::Command;

fn main(){
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

    let exit_status = Command::new("cargo".to_string())
        .arg("check")
        .args(args)
        .env("PRUSTI_QUIET", "true")
        .env("PRUSTI_FULL_COMPILATION", "true")
        .env("RUSTC_WRAPPER", prusti_rustc_path)
        .status()
        .expect("could not run cargo");

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
