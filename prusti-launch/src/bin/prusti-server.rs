// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_utils::launch;

fn main() {
    if let Err(code) = process(std::env::args().skip(1).collect()) {
        std::process::exit(code);
    }
}

fn process(args: Vec<String>) -> Result<(), i32> {
    let _setup = launch::job::setup().unwrap(); // Kill all subprocesses on kill or Ctrl-C

    let paths = launch::PrustiPaths::new();

    let mut cmd = paths.prusti_server_driver_command();
    cmd.args(args);

    // Prevent shadowing of default log behavior.
    cmd.env("DEFAULT_PRUSTI_LOG", "info");

    let exit_status = cmd.status().expect("could not run prusti-server-driver");

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
