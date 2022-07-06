// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#[cfg(target_family = "unix")]
use nix::unistd::{setpgid, Pid};
use prusti_launch::{add_to_loader_path, get_current_executable_dir, sigint_handler};
use std::{
    env,
    io::Write,
    path::{Path, PathBuf},
    process::Command,
};

fn main() {
    if let Err(code) = process(std::env::args().skip(1).collect()) {
        std::process::exit(code);
    }
}

fn process(mut args: Vec<String>) -> Result<(), i32> {
    let current_executable_dir = get_current_executable_dir();

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

    let prusti_sysroot = prusti_launch::prusti_sysroot().expect("Failed to find Rust's sysroot");

    let compiler_bin = prusti_sysroot.join("bin");
    let compiler_lib = prusti_sysroot.join("lib");

    let prusti_home = prusti_driver_path
        .parent()
        .expect("Failed to find Prusti's home");

    let mut cmd = Command::new(&prusti_driver_path);

    add_to_loader_path(vec![compiler_lib, compiler_bin, libjvm_path], &mut cmd);

    prusti_launch::set_environment_settings(&mut cmd, &current_executable_dir, &java_home);

    // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
    // We're invoking the compiler programmatically, so we ignore this
    if !args.is_empty() && Path::new(&args[0]).file_stem() == Some("rustc".as_ref()) {
        args.remove(0);
    }

    // filter out the `prusti-contracts` dependency (if present), because we will
    // replace it below with a version that is distributed with Prusti.
    if let Some(remove_index) =
        args.windows(2)
            .flat_map(<&[_; 2]>::try_from)
            .position(|[extern_flag, dependency]| {
                extern_flag == "--extern" && dependency.starts_with("prusti_contracts=")
            })
    {
        args.remove(remove_index);
        args.remove(remove_index);
    }
    cmd.args(&args);

    let has_no_sysroot_arg = !args.iter().any(|s| s == "--sysroot");
    if has_no_sysroot_arg {
        cmd.arg("--sysroot");
        cmd.arg(
            prusti_sysroot
                .into_os_string()
                .into_string()
                .expect("sysroot is not a valid utf-8 string"),
        );
    };

    // only do the following if we're not compiling the `prusti-contracts` dependency:
    if !args
        .windows(2)
        .any(|p| p == ["--crate-name", "prusti_contracts"])
    {
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
    }

    // cmd.arg("-Zreport-delayed-bugs");
    // cmd.arg("-Ztreat-err-as-bug=1");

    // Move process to group leader if it isn't
    #[cfg(target_family = "unix")]
    let _ = setpgid(Pid::this(), Pid::this());
    // Register the SIGINT handler; CTRL_C_EVENT or CTRL_BREAK_EVENT on Windows
    ctrlc::set_handler(sigint_handler).expect("Error setting Ctrl-C handler");

    if let Ok(path) = env::var("PRUSTI_RUSTC_LOG_ARGS") {
        let mut file = std::fs::File::create(path).unwrap();
        for arg in cmd.get_args() {
            writeln!(file, "{}", arg.to_str().unwrap()).unwrap();
        }
    }
    if let Ok(path) = env::var("PRUSTI_RUSTC_LOG_ENV") {
        let mut file = std::fs::File::create(path).unwrap();
        for (key, value) in cmd.get_envs() {
            writeln!(
                file,
                "{}={}",
                key.to_str().unwrap(),
                value.unwrap().to_str().unwrap()
            )
            .unwrap();
        }
    }

    let exit_status = cmd
        .status()
        .unwrap_or_else(|_| panic!("failed to execute prusti-driver ({:?})", prusti_driver_path));

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
