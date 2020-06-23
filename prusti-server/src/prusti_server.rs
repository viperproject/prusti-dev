// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//#![feature(use_extern_macros)]

extern crate prusti_launch;

use std::{path::PathBuf, process::Command};

fn main() {
    if let Err(code) = process(std::env::args().skip(1).collect()) {
        std::process::exit(code);
    }
}

fn process(args: Vec<String>) -> Result<(), i32> {
    let java_home = match std::env::var("JAVA_HOME") {
        Ok(java_home) => PathBuf::from(java_home),
        Err(_) => prusti_launch::find_java_home()
            .expect("Failed to find Java home directory. Try setting JAVA_HOME"),
    };

    let mut prusti_driver_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("prusti-server-driver");
    if cfg!(windows) {
        prusti_driver_path.set_extension("exe");
    }

    let mut cmd = Command::new(&prusti_driver_path);
    cmd.args(args);

    let libjvm_path = prusti_launch::find_libjvm(&java_home)
        .expect("Failed to find JVM library. Check JAVA_HOME");
    prusti_launch::add_to_loader_path(vec![libjvm_path], &mut cmd);

    let exit_status = cmd.status().expect("could not run prusti-server-driver");

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
