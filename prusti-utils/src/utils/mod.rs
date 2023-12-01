// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub mod identifiers;
pub mod to_string;
use std::{env, path::PathBuf};

pub fn find_compiled_executable(name: &str) -> PathBuf {
    let target_directory = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };

    let mut target_path = PathBuf::from("target");

    // If prusti was compiled for a custom target, e.g. via x.py build --target
    // <triple>, then the executables will be placed in /target/<triple>/debug
    // rather than /target/debug.

    // The environment variable COMPILATION_TARGET_PRUSTI should be set to the
    // appropriate triple when running the tests, so that executable for that
    // target is used.
    if let Ok(triple) = env::var("COMPILATION_TARGET_PRUSTI") {
        if !triple.is_empty() {
            target_path.push(triple);
        }
    }

    target_path.push(target_directory);

    let executable_name = if cfg!(windows) {
        format!("{name}.exe")
    } else {
        name.to_string()
    };

    let mut local_driver_path = target_path.clone();
    local_driver_path.push(&executable_name);

    if local_driver_path.exists() {
        return local_driver_path;
    }

    let mut workspace_driver_path = PathBuf::from("..");
    workspace_driver_path.push(target_path);
    workspace_driver_path.push(&executable_name);

    if workspace_driver_path.exists() {
        return workspace_driver_path;
    }

    panic!(
        "Could not find the {target_directory:?} {executable_name:?} binary to be used in tests. \
        It might be that the project has not been compiled correctly."
    );
}
