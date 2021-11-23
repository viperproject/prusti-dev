// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use cargo_test_support::{cargo_test, project, symlink_supported};
use std::{
    fs,
    path::{Path, PathBuf},
};

fn cargo_prusti_path() -> PathBuf {
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
            panic!(
                "Failed to canonicalize the path {:?}",
                local_prusti_rustc_path
            )
        });
    }
    let workspace_prusti_rustc_path: PathBuf = ["..", "target", target_directory, executable_name]
        .iter()
        .collect();
    if workspace_prusti_rustc_path.exists() {
        return fs::canonicalize(&workspace_prusti_rustc_path).unwrap_or_else(|_| {
            panic!(
                "Failed to canonicalize the path {:?}",
                workspace_prusti_rustc_path
            )
        });
    }
    panic!(
        "Could not find the {:?} cargo-prusti binary to be used in tests. \
        It might be that Prusti has not been compiled correctly.",
        target_directory
    );
}

#[cargo_test]
fn simple_assert_true() {
    let p = project()
        .file("src/main.rs", "fn main() { assert!(true); }")
        .build();
    p.process(cargo_prusti_path()).run();
}

#[cargo_test]
fn simple_assert_false() {
    let p = project()
        .file("src/main.rs", "fn main() { assert!(false); }")
        .build();
    p.process(cargo_prusti_path())
        .with_status(101)
        .with_stderr(
            "\
[CHECKING] foo v0.0.1 ([..])
[ERROR] [Prusti: verification error] the asserted expression might not hold
 --> src/main.rs:1:13
  |
1 | fn main() { assert!(false); }
  |             ^^^^^^^^^^^^^^
  |
  = note: this error originates in the macro `assert` (in Nightly builds, run with -Z macro-backtrace for more info)

error: could not compile `foo` due to previous error
",
        )
        .run();
}

/// Test `cargo-prusti` on one of the crates in `test/cargo_verify`.
///
/// Special files and folders in the root of the test crate:
/// * `output.stdout` and `output.stderr`: if present, they are used to check the output of
///   `cargo-prusti`.
/// * `prusti-contracts` and related Prusti crates: during the test they will link to the
///   corresponding Prusti crate.
///
/// This function requires symlinks to be supported.
///
/// For more details on the special syntax allowed in the `output.*` files, check the documentation
/// of `cargo_test_support`: <https://doc.crates.io/contrib/tests/writing.html>.
fn test_local_project<T: Into<PathBuf>>(project_name: T) {
    let mut project_builder = project().no_manifest();
    let relative_project_path = Path::new("tests/cargo_verify").join(project_name.into());
    let project_path = fs::canonicalize(&relative_project_path).unwrap_or_else(|_| {
        panic!(
            "Failed to canonicalize the path {}",
            relative_project_path.display()
        )
    });

    // Populate the test project with symlinks to the local project
    let project_path_content = fs::read_dir(&project_path)
        .unwrap_or_else(|_| panic!("Failed to read directory {}", project_path.display()));
    for entry in project_path_content {
        let entry = entry
            .unwrap_or_else(|_| panic!("Failed to read content of {}", project_path.display()));
        let path = entry.path();
        let file_name = path
            .as_path()
            .file_name()
            .unwrap_or_else(|| panic!("Failed to obtain the name of {}", path.display()));
        if file_name == "target" {
            continue;
        }
        if path.is_dir() {
            project_builder = project_builder.symlink_dir(path.as_path(), Path::new(file_name));
        } else {
            project_builder = project_builder.symlink(path.as_path(), Path::new(file_name));
        }
    }

    // Create a special symlink for prusti_contract and related Prusti crates
    let prusti_dev_path = project_path
        .parent()
        .and_then(|p| p.parent())
        .and_then(|p| p.parent())
        .and_then(|p| p.parent())
        .unwrap_or_else(|| {
            panic!(
                "Failed to obtain parent folders of {}",
                project_path.display()
            )
        });
    let prusti_contract_deps = [
        "prusti-utils",
        "prusti-specs",
        "prusti-contracts",
        "prusti-contracts-impl",
        "prusti-contracts-internal",
    ];
    for crate_name in &prusti_contract_deps {
        project_builder = project_builder.symlink_dir(
            prusti_dev_path.join(crate_name).as_path(),
            Path::new(crate_name),
        );
    }

    // Fetch dependencies using the same target folder of cargo-prusti
    let project = project_builder.build();
    project
        .process("cargo")
        .arg("build")
        .env("CARGO_TARGET_DIR", "target/verify")
        .run();

    // Set the expected exit status, stdout and stderr
    let mut test_builder = project.process(cargo_prusti_path());
    test_builder.arg("--quiet");
    let opt_expected_stdout = fs::read_to_string(project_path.join("output.stdout")).ok();
    let opt_expected_stderr = fs::read_to_string(project_path.join("output.stderr")).ok();
    if let Some(ref expected_stdout) = opt_expected_stdout {
        // In some cases, Prusti outputs more macro definitions than needed.
        // See: https://github.com/viperproject/prusti-dev/pull/762
        test_builder.with_stdout_contains(expected_stdout);
    }
    if let Some(ref expected_stderr) = opt_expected_stderr {
        test_builder.with_status(101).with_stderr(expected_stderr);
    }

    // Run the test
    test_builder.run();
}

#[cargo_test]
fn test_symlinks() {
    // Required by `test_local_project`
    assert!(symlink_supported());
}

#[cargo_test]
fn test_failing_crate() {
    test_local_project("failing_crate");
}

#[cargo_test]
fn test_no_deps() {
    test_local_project("no_deps");
}

#[cargo_test]
fn test_prusti_toml() {
    test_local_project("prusti_toml");
}

#[cargo_test]
fn test_prusti_toml_fail() {
    let old_value = if let Ok(value) = std::env::var("RUST_BACKTRACE") {
        // We need to remove this environment variable because it affects the
        // compiler output.
        std::env::remove_var("RUST_BACKTRACE");
        Some(value)
    } else {
        None
    };
    test_local_project("prusti_toml_fail");
    if let Some(value) = old_value {
        std::env::set_var("RUST_BACKTRACE", value)
    }
}

// `#![no_std]` binaries on Windows are not a thing yet,
// see <https://github.com/viperproject/prusti-dev/pull/762>.
#[cfg_attr(windows, ignore)]
#[cargo_test]
fn test_no_std() {
    test_local_project("test_no_std");
}

// TODO: automatically create a test for each folder in `test/cargo_verify`.
