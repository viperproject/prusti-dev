// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    fs,
    path::PathBuf,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc, Mutex,
    },
};
use ui_test::{default_any_file_filter, run_tests_generic, spanned::Spanned, Args, Config};

fn find_cargo_prusti_path() -> PathBuf {
    let target_directory = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    let executable_name = if cfg!(windows) {
        "cargo-prusti.exe"
    } else {
        "cargo-prusti"
    };
    let local_prusti_rustc_path: PathBuf = ["target", target_directory, executable_name]
        .iter()
        .collect();
    if local_prusti_rustc_path.exists() {
        return fs::canonicalize(&local_prusti_rustc_path).unwrap_or_else(|_| {
            panic!("Failed to canonicalize the path {local_prusti_rustc_path:?}")
        });
    }
    let workspace_prusti_rustc_path: PathBuf = ["..", "target", target_directory, executable_name]
        .iter()
        .collect();
    if workspace_prusti_rustc_path.exists() {
        return fs::canonicalize(&workspace_prusti_rustc_path).unwrap_or_else(|_| {
            panic!("Failed to canonicalize the path {workspace_prusti_rustc_path:?}")
        });
    }
    panic!(
        "Could not find the {target_directory:?} cargo-prusti binary to be used in tests. \
        It might be that Prusti has not been compiled correctly."
    );
}

fn run_cargo_tests(root_dir: &str, cargo_flags: &[&str], cargo_env: &[(&str, &str)]) {
    static ABORT_CHECK: Mutex<Option<Arc<AtomicBool>>> = Mutex::new(None);
    _ = ctrlc::try_set_handler(move || {
        if let Some(flag) = &*ABORT_CHECK.lock().unwrap() {
            flag.store(true, Ordering::Relaxed);
        }
    });

    // This setup for testing with `cargo` is loosely based on `ui_test`'s;
    // see https://github.com/oli-obk/ui_test/blob/main/tests/integration.rs

    let mut config = Config::cargo(&root_dir);

    let args = Args::test().unwrap();
    config.with_args(&args);

    *ABORT_CHECK.lock().unwrap() = Some(config.abort_check.clone());
    config.program.program = find_cargo_prusti_path();
    assert_eq!(config.program.args.remove(0), "build");
    config
        .program
        .args
        .extend(cargo_flags.iter().map(|s| s.into()));
    config
        .program
        .envs
        .push(("RUSTC_ICE".into(), Some("0".into()))); // suppress rustc-ice*.txt files
    config
        .program
        .envs
        .extend(cargo_env.iter().map(|(k, v)| (k.into(), Some(v.into()))));

    config.comment_defaults.base().require_annotations = Some(Spanned::dummy(false)).into();

    let mut config_pass = config.clone();
    config_pass.comment_defaults.base().exit_status = Some(Spanned::dummy(0)).into();

    let mut config_fail = config;
    config_fail.comment_defaults.base().exit_status = Some(Spanned::dummy(101)).into();

    let text = ui_test::status_emitter::Text::from(args.format);
    run_tests_generic(
        vec![config_pass, config_fail],
        |path, config| {
            // TODO: only these tests are currently enabled. The rest have
            //   issues that need to be fixed:
            //   - foreign_mods: "no MIR body for external fn"
            //   - library_contracts_test: AliasTy problem due to Fn type
            //   - no_deps: Prusti.toml is not taken from manifest dir
            //   - overflow_checks: missing span for overflow check
            //   - prusti_toml: Prusti.toml is not taken from manifest dir
            //   - prusti_toml_fail: Prusti.toml is not taken from manifest dir
            //   - test_no_std: needs to be updated for toolchain
            //     also: `#![no_std]` binaries on Windows are not a thing yet,
            //     see <https://github.com/viperproject/prusti-dev/pull/762>.
            //   - veribetrfs: currently broken (?)
            if !(path.ends_with("failing_crate_fail/Cargo.toml")
                || path.ends_with("failing_stable_toolchain_fail/Cargo.toml")
                || path.ends_with("simple_assert_false_fail/Cargo.toml")
                || path.ends_with("simple_assert_true/Cargo.toml"))
            {
                return None;
            }

            if !path.ends_with("Cargo.toml") {
                return None;
            }
            let file_is_fail = path
                .parent()
                .unwrap()
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .ends_with("fail");
            let config_is_fail = match config
                .comment_defaults
                .base_immut()
                .exit_status
                .as_deref()
                .unwrap()
            {
                0 => false,
                101 => true,
                _ => unreachable!(),
            };
            if file_is_fail != config_is_fail {
                return None;
            }
            Some(default_any_file_filter(path, config))
        },
        |_, _| {},
        (text,),
    )
    .unwrap();
}

pub(crate) fn run() {
    run_cargo_tests("tests/cargo_verify", &[], &[]);
}
