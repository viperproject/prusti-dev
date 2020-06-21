// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(box_syntax)]
#![feature(rustc_private)]

#[macro_use]
extern crate log;
extern crate env_logger;
extern crate prusti;
extern crate prusti_interface;
extern crate rustc_driver;

use prusti::driver_utils::run;
use prusti::prusti_runner::run_prusti;
use prusti_interface::sysroot::current_sysroot;
use rustc_driver::RustcDefaultCalls;
use std::env;
use std::path::Path;
use std::process::exit;
use prusti_interface::cargo::is_rustc_compiling_a_dependency_crate;

pub fn main() {
    env_logger::init();
    let exit_status = run(move || {
        let mut args: Vec<_> = env::args().collect();

        if args.len() <= 1 {
            std::process::exit(1);
        }

        // Disable Prusti if...
        let prusti_be_rustc = true
            // we have been called by Cargo with RUSTC_WRAPPER, and
            && (args.len() > 1 && Path::new(&args[1]).file_stem() == Some("rustc".as_ref()))
            // this is not a test, and
            && !env::var("PRUSTI_TEST").ok().map_or(false, |val| val == "true")
            // this is not the final rustc invocation, thus we are compiling a dependency
            // See: https://github.com/rust-lang-nursery/rust-clippy/issues/1066#issuecomment-440393949
            //&& !args.iter().any(|s| s.starts_with("--emit=dep-info,metadata"));
            //
            && (
                // Cargo is probably compiling a dependency
                is_rustc_compiling_a_dependency_crate(&args)
                    // Cargo is just querying for crate information
                    || args.iter().any(|arg| arg.starts_with("--print"))
            );

        // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
        // We're invoking the compiler programmatically, so we ignore this
        if Path::new(&args[1]).file_stem() == Some("rustc".as_ref()) {
            args.remove(1);
        }

        // this conditional check for the --sysroot flag is there so users can call
        // `prusti-filter` directly without having to pass --sysroot or anything
        if !args.iter().any(|s| s == "--sysroot") {
            let sys_root = current_sysroot().expect(
                "need to specify SYSROOT env var during compilation, or use rustup or multirust",
            );
            debug!("Using sys_root='{}'", sys_root);
            args.push("--sysroot".to_owned());
            args.push(sys_root);
        };

        // Early exit
        if prusti_be_rustc {
            let default_compiler_calls = Box::new(RustcDefaultCalls);
            debug!("rustc command: '{}'", args.join(" "));
            return rustc_driver::run_compiler(&args, default_compiler_calls, None, None);
        }

        run_prusti(args)
    });
    exit(exit_status as i32);
}
