// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

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
    let args = args.collect::<Vec<_>>();

    let args_manifest_path = args
        .windows(2)
        .filter_map(|w| {
            if w[0] == "--manifest-path" {
                Some(w[1].as_str())
            } else {
                None
            }
        })
        .next();

    // Category B flags (see dev-guide flags table):
    let cargo_path = config::cargo_path();
    let command = config::cargo_command();

    let features =
        if launch::enable_prusti_feature(&cargo_path, args_manifest_path) && !config::be_rustc() {
            ["--features", "prusti-contracts/prusti"].iter()
        } else {
            [].iter()
        };
    let cargo_target = env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string());
    let cargo_target: PathBuf = [cargo_target, "verify".to_string()].into_iter().collect();

    // Forward version checks directly to cargo. This is not thorough at all,
    // but matches the version check performed by `ui_test` (which itself uses
    // the `rustc_version` crate).
    if args
        .iter()
        .any(|arg| arg == "-V" || arg == "-vV" || arg == "--version")
    {
        let exit_status = Command::new(cargo_path)
            .args(args)
            .env("RUST_TOOLCHAIN", launch::get_rust_toolchain_channel())
            .env("RUSTUP_TOOLCHAIN", launch::get_rust_toolchain_channel())
            .env("RUSTC", prusti_rustc_path)
            .env("CARGO_TARGET_DIR", &cargo_target)
            .status()
            .expect("could not run cargo");
        return if exit_status.success() {
            Ok(())
        } else {
            Err(exit_status.code().unwrap_or(-1))
        };
    }

    let mut cargo_command = Command::new(cargo_path);
    cargo_command
        .arg(&command)
        .args(features)
        .args(&args)
        .env("RUST_TOOLCHAIN", launch::get_rust_toolchain_channel())
        .env("RUSTUP_TOOLCHAIN", launch::get_rust_toolchain_channel())
        .env("RUSTC", prusti_rustc_path)
        .env("PRUSTI_CARGO", "")
        .env("CARGO_TARGET_DIR", &cargo_target);
    if let Some(manifest_path) = env::var("CARGO_MANIFEST_DIR").ok().or_else(|| {
        args_manifest_path.and_then(|s| Some(PathBuf::from(s).parent()?.to_str()?.to_string()))
    }) {
        cargo_command.env("CARGO_MANIFEST_DIR", manifest_path);
    }

    // TODO: the config::* calls below are an issue: they do not respect the
    //   manifest path, if provided through `--manifest-path` instead of
    //   `CARGO_MANIFEST_DIR`. As a result, `Prusti.toml` is read from the CWD
    //   even though the `Cargo.toml` is elsewhere.

    let exit_status = cargo_command
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
                if let Some(ext) = entry.extension()
                    && ext == "specs"
                    && let Some(fname) = entry.file_name()
                {
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
    Ok(())
}
