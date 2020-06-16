// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//#![feature(use_extern_macros)]

extern crate prusti_common;

use prusti_common::driver_utils;
use std::{path::PathBuf, process::Command};

fn main() {
    if let Err(code) = process(std::env::args().skip(1).collect()) {
        std::process::exit(code);
    }
}

fn process(_args: Vec<String>) -> Result<(), i32> {
    let java_home = match std::env::var("JAVA_HOME") {
        Ok(java_home) => PathBuf::from(java_home),
        Err(_) => driver_utils::find_java_home()
            .expect("Failed to find Java home directory. Try setting JAVA_HOME"),
    };

    let mut prusti_driver_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("prusti-server-driver");
    if cfg!(windows) {
        prusti_driver_path.set_extension("exe");
    }

    let mut cmd = Command::new(&prusti_driver_path);

    /* TODO: make sure colors are used. if not, this may help.
    let has_no_color_arg = args.iter().find(|&x| x == "--color" || x.starts_with("--color=")).is_none();
    cmd.args(args);
    if has_no_color_arg {
        cmd.args(&["--color", "always"]);
    }
    */

    let libjvm_path =
        driver_utils::find_libjvm(&java_home).expect("Failed to find JVM library. Check JAVA_HOME");
    driver_utils::add_to_loader_path(vec![libjvm_path], &mut cmd);

    let exit_status = cmd.status().expect("could not run prusti-server-driver");

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
