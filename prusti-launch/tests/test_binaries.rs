// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use glob::glob;
use prusti_utils::utils::find_compiled_executable;
use std::{
    io::{BufRead, BufReader},
    path::PathBuf,
    process::{Child, Command, Stdio},
};

fn run_on_test_files<F: Fn(&PathBuf) -> Command>(run: F) {
    let mut num_pass_tests = 0;
    let pass_entries = glob("tests/pass/**/*.rs").expect("failed to read glob pattern");
    for entry in pass_entries {
        let path = entry.unwrap();
        num_pass_tests += 1;
        let mut cmd = run(&path);
        println!("Running {cmd:?}");
        let output = cmd
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute process: {err:?}"));
        if !output.status.success() {
            println!("Test case {path:?} unexpectedly failed.");
            println!("Exit status: {:?}", output.status);
            println!("┌─── Begin of stdout ───┐");
            println!("{}", String::from_utf8_lossy(&output.stdout));
            println!("└──── End of stdout ────┘");
            println!("┌─── Begin of stderr ───┐");
            println!("{}", String::from_utf8_lossy(&output.stderr));
            println!("└──── End of stderr ────┘");
            panic!("Test case unexpectedly failed. See the output for details.");
        }
    }
    assert!(num_pass_tests >= 2);

    let mut num_fail_tests = 0;
    let fail_entries = glob("tests/fail/**/*.rs").expect("failed to read glob pattern");
    for entry in fail_entries {
        let path = entry.unwrap();
        num_fail_tests += 1;
        let mut cmd = run(&path);
        println!("Running {cmd:?}");
        let output = cmd
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .unwrap_or_else(|err| panic!("Failed to execute process: {err:?}"));
        if output.status.success() {
            println!("Test case {path:?} unexpectedly succeeded.");
            println!("Exit status: {:?}", output.status);
            println!("┌─── Begin of stdout ───┐");
            println!("{}", String::from_utf8_lossy(&output.stdout));
            println!("└──── End of stdout ────┘");
            println!("┌─── Begin of stderr ───┐");
            println!("{}", String::from_utf8_lossy(&output.stderr));
            println!("└──── End of stderr ────┘");
            panic!("Test case unexpectedly failed. See the output for details.");
        }
    }
    assert!(num_fail_tests >= 2);
}

/// Kill a spawned Child process even in case of panics.
struct ChildGuard(Child);

impl Drop for ChildGuard {
    fn drop(&mut self) {
        if let Err(e) = self.0.kill() {
            panic!("Could not kill child process: {e}");
        }
    }
}

#[test]
fn test_prusti_rustc() {
    let prusti_rustc = find_compiled_executable("prusti-rustc");

    run_on_test_files(|program: &PathBuf| {
        let mut cmd = Command::new(&prusti_rustc);
        cmd.arg("--edition=2018")
            .arg(program)
            .env("PRUSTI_LOG", "info")
            .env("RUST_BACKTRACE", "1");
        cmd
    });
}

#[test]
fn test_prusti_rustc_dump() {
    let prusti_rustc = find_compiled_executable("prusti-rustc");

    run_on_test_files(|program: &PathBuf| {
        let mut cmd = Command::new(&prusti_rustc);
        cmd.arg("--edition=2018")
            .arg(program)
            .env("PRUSTI_DUMP_DEBUG_INFO", "true")
            .env("PRUSTI_DUMP_DEBUG_INFO_DURING_FOLD", "true")
            .env("PRUSTI_DUMP_PATH_CTXT_IN_DEBUG_INFO", "true")
            .env("PRUSTI_DUMP_REBORROWING_DAG_IN_DEBUG_INFO", "true")
            .env("PRUSTI_DUMP_BORROWCK_INFO", "true")
            .env("PRUSTI_DUMP_VIPER_PROGRAM", "true")
            .env("PRUSTI_PRINT_DESUGARED_SPECS", "true")
            .env("PRUSTI_PRINT_TYPECKD_SPECS", "true")
            .env("PRUSTI_LOG", "info")
            .env("RUST_BACKTRACE", "1");
        cmd
    });
}

/*
// The `PRUSTI_BE_RUSTC` flag doesn't change the behaviour of Prusti macros
// so this test fails.
#[test]
fn test_prusti_be_rustc() {
    let prusti_rustc = find_compiled_executable("prusti-rustc");

    run_on_test_files(|program: &PathBuf| {
        let mut cmd = Command::new(&prusti_rustc);
        cmd.arg("--edition=2018")
            .arg(program)
            .env("PRUSTI_BE_RUSTC", "true")
            .env("PRUSTI_LOG", "info")
            .env("RUST_BACKTRACE", "1");
        cmd
    });
}
*/

#[test]
fn test_prusti_rustc_with_server() {
    let prusti_rustc = find_compiled_executable("prusti-rustc");
    let prusti_server = find_compiled_executable("prusti-server");

    // Preserve SYSTEMROOT on Windows.
    // See: https://travis-ci.community/t/socket-the-requested-service-provider-could-not-be-loaded-or-initialized/1127
    let mut server_child = Command::new(prusti_server)
        .env("PRUSTI_LOG", "warn")
        .env("RUST_BACKTRACE", "1")
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed to start prusti-server");

    // Wait for the server to be ready and read the server port
    let server_port = {
        let mut opt_server_port = None;
        let stdout = server_child.stdout.as_mut().unwrap();
        let stdout_reader = BufReader::new(stdout);
        let stdout_lines = stdout_reader.lines();

        for result in stdout_lines {
            match result {
                Err(why) => panic!("could not read from prusti-server's stdout: {why}"),
                Ok(line) => {
                    if let Some(port) = line.strip_prefix("port: ") {
                        opt_server_port = Some(port.to_string());
                        break;
                    }
                }
            }
        }
        opt_server_port.expect("failed to read prusti-server port")
    };

    let _server_child_guard = ChildGuard(server_child);

    run_on_test_files(|program: &PathBuf| {
        let mut cmd = Command::new(&prusti_rustc);
        cmd.arg("--edition=2018")
            .arg(program)
            .env("PRUSTI_LOG", "info")
            .env("RUST_BACKTRACE", "1")
            .env("PRUSTI_SERVER_ADDRESS", format!("localhost:{server_port}"));
        cmd
    });
}
