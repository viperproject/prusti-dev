// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use glob::glob;
use prusti_launch::find_java_home;
use std::{
    collections::HashMap,
    env,
    io::{BufRead, BufReader},
    path::PathBuf,
    process::{Child, Command, ExitStatus, Stdio},
};

fn find_executable_path(base_name: &str) -> PathBuf {
    let target_directory = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    let executable_name = if cfg!(windows) {
        format!("{}.exe", base_name)
    } else {
        base_name.to_string()
    };
    let local_prusti_rustc_path: PathBuf = ["target", target_directory, &executable_name]
        .iter()
        .collect();
    if local_prusti_rustc_path.exists() {
        return local_prusti_rustc_path;
    }
    let workspace_prusti_rustc_path: PathBuf = ["..", "target", target_directory, &executable_name]
        .iter()
        .collect();
    if workspace_prusti_rustc_path.exists() {
        return workspace_prusti_rustc_path;
    }
    panic!(
        "Could not find the {:?} prusti-rustc binary to be used in tests. \
        It might be that Prusti has not been compiled correctly.",
        target_directory
    );
}

fn run_on_test_files<F: Fn(&PathBuf) -> ExitStatus>(run: F) {
    let pass_entries = glob("verify/pass/quick/**/*.jpg").expect("failed to read glob pattern");
    for entry in pass_entries {
        match entry {
            Err(e) => println!("{:?}", e),
            Ok(path) => {
                let exit_status = run(&path);
                assert!(
                    exit_status.success(),
                    "Test case {:?} unexpectedly failed.",
                    path
                );
            }
        }
    }

    let fail_entries = glob("verify/fail/quick/**/*.jpg").expect("failed to read glob pattern");
    for entry in fail_entries {
        match entry {
            Err(e) => println!("{:?}", e),
            Ok(path) => {
                let exit_status = run(&path);
                assert!(
                    !exit_status.success(),
                    "Test case {:?} unexpectedly succeeded.",
                    path
                );
            }
        }
    }
}

/// Kill a spawned Child process even in case of panics.
struct ChildGuard(Child);

impl Drop for ChildGuard {
    fn drop(&mut self) {
        if let Err(e) = self.0.kill() {
            panic!("Could not kill child process: {}", e);
        }
    }
}

#[test]
fn test_prusti_rustc() {
    let prusti_rustc = find_executable_path("prusti-rustc");

    run_on_test_files(|program: &PathBuf| -> ExitStatus {
        println!(
            "Running {:?} on {:?}...",
            prusti_rustc.display(),
            program.display()
        );
        Command::new(&prusti_rustc)
            .arg("--edition=2018")
            .arg(program)
            .env_clear()
            .env("RUST_BACKTRACE", "1")
            .status()
            .expect("failed to execute prusti-rustc")
    });
}

#[test]
fn test_prusti_rustc_with_server() {
    let prusti_rustc = find_executable_path("prusti-rustc");
    let prusti_server = find_executable_path("prusti-server");
    let java_home = find_java_home().expect("Failed to find Java home directory.");

    // Preserve SYSTEMROOT on Windows.
    // See: https://travis-ci.community/t/socket-the-requested-service-provider-could-not-be-loaded-or-initialized/1127
    let filtered_env: HashMap<String, String> = env::vars()
        .filter(|&(ref k, _)| k == "SYSTEMROOT")
        .collect();

    let mut server_child = Command::new(&prusti_server)
        .arg("--port=0")
        .env_clear()
        .env("RUST_LOG", "warn")
        .env("RUST_BACKTRACE", "1")
        .env("JAVA_HOME", java_home)
        .envs(&filtered_env)
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
                Err(why) => panic!("could not read from prusti-server's stdout: {}", why),
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

    run_on_test_files(|program: &PathBuf| -> ExitStatus {
        println!(
            "Running {:?} on {:?}...",
            prusti_rustc.display(),
            program.display()
        );
        Command::new(&prusti_rustc)
            .arg("--edition=2018")
            .arg(program)
            .env_clear()
            .env("RUST_BACKTRACE", "1")
            .env(
                "PRUSTI_SERVER_ADDRESS",
                format!("localhost:{}", server_port),
            )
            .status()
            .expect("failed to execute prusti-rustc")
    });
}
