// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_launch::{enable_prusti_feature, get_rust_toolchain_channel};
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

    // Remove the "prusti" argument when `cargo-prusti` is invocated
    // as `cargo --cflag prusti -flag` (note the space rather than `-`)
    let args = args.skip_while(|arg| arg == "prusti");

    let cargo_path = env::var("CARGO_PATH").unwrap_or_else(|_| "cargo".to_string());

    let mut cargo_target =
        PathBuf::from(env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string()));
    cargo_target.push("verify");
    let command = env::var("CARGO_PRUSTI_COMMAND").unwrap_or_else(|_| "check".to_string());
    let features = if enable_prusti_feature(&cargo_path) {
        ["--features", "prusti-contracts/prusti"].iter()
    } else {
        [].iter()
    };
    let exit_status = Command::new(cargo_path)
        .arg(&command)
        .args(args)
        .args(features)
        .env("RUST_TOOLCHAIN", get_rust_toolchain_channel())
        .env("RUSTC_WRAPPER", prusti_rustc_path)
        .env("DEFAULT_PRUSTI_QUIET", "true")
        .env("DEFAULT_PRUSTI_FULL_COMPILATION", "true")
        .env("DEFAULT_PRUSTI_LOG_DIR", cargo_target.join("log"))
        .env("DEFAULT_PRUSTI_CACHE_PATH", cargo_target.join("cache.bin"))
        .env("CARGO_TARGET_DIR", &cargo_target)
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
