// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use cargo_test_support::{cargo_test, project, symlink_supported};
use std::path::{Path, PathBuf};
use std::fs;

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
    let local_prusti_rustc_path: PathBuf = ["target", target_directory, executable_name].iter().collect();
    if local_prusti_rustc_path.exists() {
        return fs::canonicalize(&local_prusti_rustc_path).expect(
            &format!("Failed to canonicalize the path {:?}", local_prusti_rustc_path)
        );
    }
    let workspace_prusti_rustc_path: PathBuf = ["..", "target", target_directory, executable_name].iter().collect();
    if workspace_prusti_rustc_path.exists() {
        return fs::canonicalize(&workspace_prusti_rustc_path).expect(
            &format!("Failed to canonicalize the path {:?}", workspace_prusti_rustc_path)
        );
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
    p.process(cargo_prusti_path())
        .run();
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
SLF4J: Class path contains multiple SLF4J bindings.
SLF4J: Found binding in [jar:file:[..]]
SLF4J: Found binding in [jar:file:[..]]
SLF4J: See http://www.slf4j.org/codes.html#multiple_bindings for an explanation.
SLF4J: Actual binding is of type [ch.qos.logback.classic.util.ContextSelectorStaticBinder]
[ERROR] [Prusti: verification error] the asserted expression might not hold
 --> src/main.rs:1:13
  |
1 | fn main() { assert!(false); }
  |             ^^^^^^^^^^^^^^^
  |
  = note: this error originates in the macro `assert` (in Nightly builds, run with -Z macro-backtrace for more info)

[ERROR] aborting due to previous error

[ERROR] could not compile `foo`

To learn more, run the command again with --verbose.
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
    let project_path = fs::canonicalize(&relative_project_path).expect(
        &format!("Failed to canonicalize the path {}", relative_project_path.display())
    );

    // Populate the test project with symlinks to the local project
    let project_path_content = fs::read_dir(&project_path)
        .expect(&format!("Failed to read directory {}", project_path.display()));
    for entry in project_path_content {
        let entry = entry.expect(&format!("Failed to read content of {}", project_path.display()));
        let path = entry.path();
        let file_name = path.as_path().file_name()
            .expect(&format!("Failed to obtain the name of {}", path.display()));
        if path.is_dir() {
            project_builder = project_builder.symlink_dir(path.as_path(), &Path::new(file_name));
        } else {
            project_builder = project_builder.symlink(path.as_path(), &Path::new(file_name));
        }
    }

    // Create a special symlink for prusti_contract and related Prusti crates
    let prusti_dev_path = project_path
        .parent()
        .and_then(|p| p.parent())
        .and_then(|p| p.parent())
        .and_then(|p| p.parent())
        .expect(&format!("Failed to obtain parent folders of {}", project_path.display()));
    let prusti_contract_deps = [
        "prusti-specs",
        "prusti-contracts",
        "prusti-contracts-impl",
        "prusti-contracts-internal",
    ];
    for crate_name in &prusti_contract_deps {
        project_builder = project_builder.symlink_dir(
            prusti_dev_path.join(crate_name).as_path(),
            &Path::new(crate_name)
        );
    }

    // Fetch dependencies
    let project = project_builder.build();
    project.process("cargo").arg("build").run();

    // Set the expected exit status, stdout and stderr
    let mut test_builder = project.process(cargo_prusti_path());
    let opt_expected_stdout = fs::read_to_string(project_path.join("output.stdout")).ok();
    let opt_expected_stderr = fs::read_to_string(project_path.join("output.stderr")).ok();
    if let Some(ref expected_stdout) = opt_expected_stdout {
        test_builder.with_stdout(expected_stdout);
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

// TODO: automatically create a test for each folder in `test/cargo_verify`.
