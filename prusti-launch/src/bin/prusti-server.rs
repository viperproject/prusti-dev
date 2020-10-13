// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

extern crate prusti_launch;

use std::{env, path::PathBuf, process::Command};
use prusti_launch::{find_viper_home, find_z3_exe};

fn main() {
    if let Err(code) = process(std::env::args().skip(1).collect()) {
        std::process::exit(code);
    }
}

fn process(args: Vec<String>) -> Result<(), i32> {
    let current_executable_dir = env::current_exe()
        .expect("current executable path invalid")
        .parent()
        .expect("failed to obtain the folder of the current executable")
        .to_path_buf();

    let mut prusti_server_driver_path = current_executable_dir.join("prusti-server-driver");
    if cfg!(windows) {
        prusti_server_driver_path.set_extension("exe");
    }

    let java_home = match std::env::var("JAVA_HOME") {
        Ok(java_home) => PathBuf::from(java_home),
        Err(_) => prusti_launch::find_java_home()
            .expect("Failed to find Java home directory. Try setting JAVA_HOME"),
    };

    let mut cmd = Command::new(&prusti_server_driver_path);
    cmd.args(args);

    let libjvm_path = prusti_launch::find_libjvm(&java_home)
        .expect("Failed to find JVM library. Check JAVA_HOME");
    prusti_launch::add_to_loader_path(vec![libjvm_path], &mut cmd);

    if let None = env::var("VIPER_HOME").ok() {
        if let Some(viper_home) = find_viper_home(&current_executable_dir) {
            cmd.env("VIPER_HOME", viper_home);
        } else {
            panic!(
                "Could not find the Viper home. \
                Please set the VIPER_HOME environment variable, which should contain the path of \
                the folder that contains all Viper JAR files."
            );
        }
    };

    if let None = env::var("Z3_EXE").ok() {
        if let Some(z3_exe) = find_z3_exe(&current_executable_dir) {
            cmd.env("Z3_EXE", z3_exe);
        } else {
            panic!(
                "Could not find the Z3 executable. \
                Please set the Z3_EXE environment variable, which should contain the path of a \
                Z3 executable."
            );
        }
    };

    let exit_status = cmd.status().expect("could not run prusti-server-driver");

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
