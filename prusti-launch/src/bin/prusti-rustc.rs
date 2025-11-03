// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_utils::launch;
use std::{env, io::Write};

fn main() {
    if let Err(code) = process(std::env::args().skip(1).collect()) {
        std::process::exit(code);
    }
}

fn process(mut args: Vec<String>) -> Result<(), i32> {
    let _setup = launch::job::setup().unwrap(); // Kill all subprocesses on kill or Ctrl-C

    let paths = launch::PrustiPaths::new();

    let mut cmd = paths.prusti_driver_command();
    cmd.arg("--cfg=prusti");

    let prusti_sysroot = launch::prusti_sysroot().expect("Failed to find Rust's sysroot");

    let cargo_invoked = env::var("PRUSTI_CARGO").is_ok();

    // No need to check if we happen to be running on e.g. the `prusti-contracts` crate since this
    // should always be with `cargo` anyway (i.e. cargo_invoked == true)
    if !cargo_invoked {
        // Need to give references to standard prusti libraries
        let target_dir = launch::get_prusti_contracts_dir(paths.current_executable_dir())
            .unwrap_or_else(|| {
                panic!(
                    "Failed to find the path of the Prusti contracts from prusti home '{}'",
                    paths.current_executable_dir().display()
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
                    illegal_arg[0], illegal_arg[1],
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

        // Avoid need for `main` function when running `prusti-rustc` directly
        if !args.iter().any(|s| s.starts_with("--crate-type=")) {
            args.push("--crate-type=lib".into());
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
        .unwrap_or_else(|e| panic!("failed to execute prusti-driver: {e}"));

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
