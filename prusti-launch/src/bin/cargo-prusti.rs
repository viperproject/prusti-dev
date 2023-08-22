// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![feature(let_chains)]

use prusti_utils::{config, launch};
use std::{env, fs, io, path::PathBuf, process::Command};

fn main() {
    if let Err(code) = process(env::args().skip(1)) {
        std::process::exit(code);
    }
}

fn process<I>(args: I) -> Result<(), i32>
where
    I: Iterator<Item = String>,
{
    let mut prusti_rustc_path = env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("prusti-rustc");
    if cfg!(windows) {
        prusti_rustc_path.set_extension("exe");
    }

    // Remove the "prusti" argument when `cargo-prusti` is invoked as
    // `cargo --cflag prusti -- -Pflag` (note the space in `cargo prusti` rather than a `-`)
    let args = args.skip_while(|arg| arg == "prusti");
    // Remove the "-- -Pflag" arguments since these won't apply to `cargo check`.
    // They have already been loaded (and the Category B flags are used below).
    let args = args.take_while(|arg| arg != "--");

    // Category B flags (see dev-guide flags table):
    let cargo_path = config::cargo_path();
    let command = config::cargo_command();

    let features = if launch::enable_prusti_feature(&cargo_path) && !config::be_rustc() {
        ["--features", "prusti-contracts/prusti"].iter()
    } else {
        [].iter()
    };
    let cargo_target = env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string());
    let cargo_target: PathBuf = [cargo_target, "verify".to_string()].into_iter().collect();
    let exit_status = Command::new(cargo_path)
        .arg(&command)
        .args(features)
        .args(args)
        .env("RUST_TOOLCHAIN", launch::get_rust_toolchain_channel())
        .env("RUSTUP_TOOLCHAIN", launch::get_rust_toolchain_channel())
        .env("RUSTC", prusti_rustc_path)
        .env("PRUSTI_CARGO", "")
        .env("CARGO_TARGET_DIR", &cargo_target)
        // Category B flags (update the docs if any more are added):
        .env("PRUSTI_BE_RUSTC", config::be_rustc().to_string())
        .env(
            "PRUSTI_NO_VERIFY_DEPS",
            config::no_verify_deps().to_string(),
        )
        // Category A* flags:
        .env("DEFAULT_PRUSTI_QUIET", "true")
        .env("DEFAULT_PRUSTI_FULL_COMPILATION", "true")
        .env("DEFAULT_PRUSTI_LOG_DIR", cargo_target.join("log"))
        .env("DEFAULT_PRUSTI_CACHE_PATH", cargo_target.join("cache.bin"))
        .status()
        .expect("could not run cargo");

    if exit_status.success() {
        if command == "build" {
            copy_exported_specs(cargo_target).ok();
        }
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}

/// Copy specs from '{cargo_target}/*/deps/*.specs' to '{cargo_target}/*/*.specs'
fn copy_exported_specs(cargo_target: PathBuf) -> io::Result<()> {
    for de in fs::read_dir(cargo_target)? {
        let build_dir = de?.path();
        let deps_dir = build_dir.join("deps");
        if build_dir.is_dir() && deps_dir.is_dir() {
            for entry in fs::read_dir(deps_dir)? {
                let entry = entry?.path();
                if let Some(ext) = entry.extension() && ext == "specs" {
                    if let Some(fname) = entry.file_name() {
                        let pkg_name = fname.to_string_lossy();
                        if let Some(pkg_name) = pkg_name.split('-').next() {
                            let mut tgt = build_dir.join(pkg_name);
                            tgt.set_extension("specs");
                            fs::copy(entry, tgt)?;
                        }
                    }
                }
            }
        }
    }
    Ok(())
}
