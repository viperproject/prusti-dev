// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#[cfg(target_family = "unix")]
use nix::unistd::{setpgid, Pid};
use prusti_utils::launch;
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
    let prusti_home = launch::get_current_executable_dir();

    let mut prusti_driver_path = prusti_home.join("prusti-driver");
    if cfg!(windows) {
        prusti_driver_path.set_extension("exe");
    }

    let java_home = match env::var("JAVA_HOME") {
        Ok(java_home) => PathBuf::from(java_home),
        Err(_) => launch::find_java_home()
            .expect("Failed to find Java home directory. Try setting JAVA_HOME"),
    };

    let libjvm_path =
        launch::find_libjvm(&java_home).expect("Failed to find JVM library. Check JAVA_HOME");

    let prusti_sysroot = launch::prusti_sysroot().expect("Failed to find Rust's sysroot");

    let compiler_bin = prusti_sysroot.join("bin");
    let compiler_lib = prusti_sysroot.join("lib");

    let mut cmd = Command::new(&prusti_driver_path);

    launch::add_to_loader_path(vec![compiler_lib, compiler_bin, libjvm_path], &mut cmd);

    launch::set_environment_settings(&mut cmd, &prusti_home, &java_home);

    // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
    // We're invoking the compiler programmatically, so we ignore this
    let rustc_pos = args
        .iter()
        .position(|arg| Path::new(arg).file_stem() == Some("rustc".as_ref()));
    let cargo_invoked = rustc_pos.is_some();
    if let Some(rustc_pos) = rustc_pos {
        args.drain(0..=rustc_pos);
    }

    // No need to check if we happen to be running on e.g. the `prusti-contracts` crate since this
    // should always be with `cargo` anyway (i.e. cargo_invoked == true)
    if !cargo_invoked {
        // Need to give references to standard prusti libraries
        let target_dir = launch::get_prusti_contracts_dir(&prusti_home).unwrap_or_else(|| {
            panic!(
                "Failed to find the path of the Prusti contracts from prusti home '{}'",
                prusti_home.display()
            )
        });
        if target_dir.to_str().is_none() {
            panic!(
                "Path to '{}' is not a valid utf-8 string!",
                target_dir.to_string_lossy()
            );
        }

        // This is where the files we'll link against live
        args.push("-L".into());
        args.push(format!(
            "dependency={}",
            target_dir.join("deps").to_str().unwrap()
        ));

        for prusti_lib in launch::PRUSTI_LIBS.map(|c| c.replace('-', "_")) {
            if let Some(illegal_arg) = args
                .windows(2)
                .find(|p| p[0] == "--extern" && p[1].starts_with(&format!("{prusti_lib}=")))
            {
                panic!(
                    "Running `prusti-rustc` with the flag '{} {}' is not supported! \
                    The crate `{prusti_lib}` is an internal Prusti crate and will be linked automatically. \
                    If you encounter this error running with `cargo(-prusti)` please file a bug report.",
                    illegal_arg[0],
                    illegal_arg[1],
                );
            }
            // These are the libraries that files compiled with prusti-rustc get
            args.push("--extern".into());
            let lib_file = format!("lib{prusti_lib}.rlib");
            args.push(format!(
                "{prusti_lib}={}",
                target_dir.join(lib_file).to_str().unwrap()
            ));
        }
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

    // cmd.arg("-Zreport-delayed-bugs");
    // cmd.arg("-Ztreat-err-as-bug=1");

    // Move process to group leader if it isn't
    #[cfg(target_family = "unix")]
    let _ = setpgid(Pid::this(), Pid::this());
    // Register the SIGINT handler; CTRL_C_EVENT or CTRL_BREAK_EVENT on Windows
    ctrlc::set_handler(launch::sigint_handler).expect("Error setting Ctrl-C handler");

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
        .unwrap_or_else(|_| panic!("failed to execute prusti-driver ({prusti_driver_path:?})"));

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
