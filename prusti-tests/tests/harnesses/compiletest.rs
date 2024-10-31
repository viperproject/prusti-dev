// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]

// use log::{error, info};
use prusti_server::spawn_server_thread;
use std::{
    env,
    path::PathBuf,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc, Mutex,
    },
};
use ui_test::{run_tests, spanned::Spanned, Config};

fn find_prusti_rustc_path() -> PathBuf {
    let target_directory = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    let executable_name = if cfg!(windows) {
        "prusti-rustc.exe"
    } else {
        "prusti-rustc"
    };
    let local_prusti_rustc_path: PathBuf = ["target", target_directory, executable_name]
        .iter()
        .collect();
    if local_prusti_rustc_path.exists() {
        return local_prusti_rustc_path;
    }
    let workspace_prusti_rustc_path: PathBuf = ["..", "target", target_directory, executable_name]
        .iter()
        .collect();
    if workspace_prusti_rustc_path.exists() {
        return workspace_prusti_rustc_path;
    }
    panic!(
        "Could not find the {target_directory:?} prusti-rustc binary to be used in tests. \
        It might be that Prusti has not been compiled correctly."
    );
}

fn run_prusti_tests(
    group_name: &str,
    rustc_flags: &[&str],
    rustc_env: &[(&str, &str)],
) -> ui_test::color_eyre::Result<()> {
    static ABORT_CHECK: Mutex<Option<Arc<AtomicBool>>> = Mutex::new(None);
    _ = ctrlc::try_set_handler(move || {
        if let Some(flag) = &*ABORT_CHECK.lock().unwrap() {
            flag.store(true, Ordering::Relaxed);
        }
    });

    let prusti_config = |path| {
        let mut config = Config::rustc(&path);
        *ABORT_CHECK.lock().unwrap() = Some(config.abort_check.clone());
        config.program.program = find_prusti_rustc_path();
        config
            .program
            .args
            .extend(rustc_flags.iter().map(|s| s.into()));
        config
            .program
            .envs
            .push(("RUSTC_ICE".into(), Some("0".into()))); // suppress rustc-ice*.txt files
        config
            .program
            .envs
            .extend(rustc_env.iter().map(|(k, v)| (k.into(), Some(v.into()))));
        config
    };

    // UI
    {
        let config = prusti_config(format!("tests/{group_name}/ui"));
        // "--color=never {}"
        run_tests(config)?;
    }

    // fail
    {
        let mut config = prusti_config(format!("tests/{group_name}/fail"));
        config.comment_defaults.base().normalize_stderr.push((
            ui_test::Match::Regex(regex::bytes::Regex::new(".*\n").unwrap()),
            b"".into(),
        ));
        run_tests(config)?;
    }

    // pass
    {
        let mut config = prusti_config(format!("tests/{group_name}/pass"));
        config.comment_defaults.base().exit_status = Spanned::dummy(0).into();
        config.comment_defaults.base().require_annotations = Spanned::dummy(false).into();
        run_tests(config)?;
    }

    Ok(())
}

fn run_no_verification(group_name: &str) {
    run_prusti_tests(
        group_name,
        &[],
        &[
            ("PRUSTI_FULL_COMPILATION", "true"),
            ("PRUSTI_NO_VERIFY", "true"),
            ("PRUSTI_QUIET", "true"),
        ],
    )
    .unwrap();
}

fn run_verification_no_overflow(group_name: &str) {
    run_prusti_tests(
        group_name,
        &["-Awarnings"],
        &[
            ("PRUSTI_FULL_COMPILATION", "true"),
            ("PRUSTI_QUIET", "true"),
            ("PRUSTI_CHECK_OVERFLOWS", "false"),
        ],
    )
    .unwrap();
}

fn run_verification_overflow(group_name: &str) {
    run_prusti_tests(
        group_name,
        &["-Awarnings"],
        &[
            ("PRUSTI_FULL_COMPILATION", "true"),
            ("PRUSTI_QUIET", "true"),
        ],
    )
    .unwrap();
}

fn run_verification_core_proof(group_name: &str) {
    run_prusti_tests(
        group_name,
        &["-Awarnings"],
        &[
            ("PRUSTI_FULL_COMPILATION", "true"),
            ("PRUSTI_QUIET", "true"),
            ("PRUSTI_CHECK_PANICS", "false"),
            ("PRUSTI_CHECK_OVERFLOWS", "false"),
        ],
    )
    .unwrap();
}

fn run_lifetimes_dump(group_name: &str) {
    run_prusti_tests(
        group_name,
        &[],
        &[
            ("PRUSTI_NO_VERIFY", "true"),
            ("PRUSTI_DUMP_BORROWCK_INFO", "true"),
            ("PRUSTI_QUIET", "true"),
        ],
    )
    .unwrap();
}

pub(crate) fn run() {
    // Spawn server process as child (so it stays around until main function terminates)
    let server_address = spawn_server_thread();
    env::set_var("PRUSTI_SERVER_ADDRESS", server_address.to_string());

    // Run (temporary) tests specific to Prusti v2.
    println!("[v2]");
    run_verification_no_overflow("v2");
    /*
        let save_verification_cache =
            || match ureq::post(&format!("http://{server_address}/save")).call() {
                Ok(response) => {
                    info!("Saving verification cache: {}", response.status_text());
                }
                Err(ureq::Error::Status(_code, response)) => {
                    error!("Error while saving verification cache: {response:?}");
                }
                Err(err) => error!("Error while saving verification cache: {err}"),
            };

        // Test the parsing of specifications. This doesn't run the verifier.
        println!("[parse]");
        run_no_verification("parse");

        // Test the type-checking of specifications. This doesn't run the verifier.
        println!("[typecheck]");
        run_no_verification("typecheck");

        // Test the verifier.
        println!("[verify]");
        run_verification_no_overflow("verify");
        save_verification_cache();

        // Test the verifier with overflow checks enabled.
        println!("[verify_overflow]");
        run_verification_overflow("verify_overflow");
        save_verification_cache();

        // Test the verifier with test cases that only partially verify due to known open issues.
        // The purpose of these tests is two-fold: 1. these tests help prevent potential further
        // regressions, because the tests also test code paths not covered by other tests; and
        // 2. a failing test without any errors notifies the developer when a proper fix is in
        // place. In this case, these test can be moved to the `verify/pass/` or
        // `verify_overflow/pass` folders.
        println!("[verify_partial]");
        run_verification_overflow("verify_partial");
        save_verification_cache();

        // Test the verifier with panic checks disabled (i.e. verify only the core proof).
        println!("[core_proof]");
        run_verification_core_proof("core_proof");
        save_verification_cache();

        // Test the verifier with panic checks disabled (i.e. verify only the core proof).
        println!("[lifetimes_dump]");
        run_lifetimes_dump("lifetimes_dump");
        save_verification_cache();
    */
}
