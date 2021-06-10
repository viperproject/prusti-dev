// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{env, path::{Path, PathBuf}, process::Command};
use prusti_launch::{add_to_loader_path, find_viper_home, find_z3_exe, sigint_handler};
#[cfg(target_family = "unix")]
use nix::unistd::{setpgid, Pid};

fn main() {
    if let Err(code) = process(std::env::args().skip(1).collect()) {
        std::process::exit(code);
    }
}

fn process(mut args: Vec<String>) -> Result<(), i32> {
    let current_executable_dir = env::current_exe()
        .expect("current executable path invalid")
        .parent()
        .expect("failed to obtain the folder of the current executable")
        .to_path_buf();

    let mut prusti_driver_path = current_executable_dir.join("prusti-driver");
    if cfg!(windows) {
        prusti_driver_path.set_extension("exe");
    }

    let java_home = match env::var("JAVA_HOME") {
        Ok(java_home) => PathBuf::from(java_home),
        Err(_) => prusti_launch::find_java_home()
            .expect("Failed to find Java home directory. Try setting JAVA_HOME"),
    };

    let libjvm_path = prusti_launch::find_libjvm(&java_home)
        .expect("Failed to find JVM library. Check JAVA_HOME");

    let prusti_sysroot = prusti_launch::prusti_sysroot()
        .expect(&format!("Failed to find Rust's sysroot for Prusti"));

    let compiler_bin = prusti_sysroot.join("bin");
    let compiler_lib = prusti_sysroot.join("lib");

    let prusti_home = prusti_driver_path
        .parent()
        .expect("Failed to find Prusti's home");

    let mut cmd = Command::new(&prusti_driver_path);

    add_to_loader_path(vec![compiler_lib, compiler_bin, libjvm_path], &mut cmd);

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

    let has_no_sysroot_arg = !args.iter().any(|s| s == "--sysroot");

    // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
    // We're invoking the compiler programmatically, so we ignore this
    if args.len() > 0 && Path::new(&args[0]).file_stem() == Some("rustc".as_ref()) {
        args.remove(0);
    }

    cmd.args(args);

    if has_no_sysroot_arg {
        cmd.arg("--sysroot".to_string());
        cmd.arg(
            prusti_sysroot
                .into_os_string()
                .into_string()
                .expect("sysroot is not a valid utf-8 string"),
        );
    };

    cmd.arg("-L");
    cmd.arg(format!(
        "dependency={}",
        prusti_home
            .join("deps")
            .as_os_str()
            .to_str()
            .expect("the Prusti HOME path contains invalid UTF-8")
    ));

    cmd.arg("--extern");
    let prusti_contracts_path = prusti_home.join("libprusti_contracts.rlib");
    cmd.arg(format!(
        "prusti_contracts={}",
        prusti_contracts_path
            .as_os_str()
            .to_str()
            .expect("the Prusti contracts path contains invalid UTF-8")
    ));

    // Set the `prusti` compilation flag, used to enable `prusti_contract`'s macros.
    cmd.arg("--cfg=feature=\"prusti\"");

    // cmd.arg("-Zreport-delayed-bugs");
    // cmd.arg("-Ztreat-err-as-bug=1");

    // Move process to group leader if it isn't
    #[cfg(target_family = "unix")]
    let _ = setpgid(Pid::this(), Pid::this());
    // Register the SIGINT handler; CTRL_C_EVENT or CTRL_BREAK_EVENT on Windows
    ctrlc::set_handler(sigint_handler).expect("Error setting Ctrl-C handler");

    let exit_status = cmd.status()
        .expect(&format!("failed to execute prusti-driver ({:?})", prusti_driver_path));

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
