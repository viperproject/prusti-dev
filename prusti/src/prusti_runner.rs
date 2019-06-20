// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use compiler_calls::PrustiCompilerCalls;
use prusti_interface::config;
use rustc::session::CompileResult;
use rustc::session::Session;
use rustc_driver;
use std::env;

/// Add arguments required by Prusti, then run the compiler with Prusti callbacks
pub fn run_prusti(mut args: Vec<String>) -> (CompileResult, Option<Session>) {
    // TODO: Switch to opt because Naive does not compute borrows.
    //env::set_var("POLONIUS_ALGORITHM", "DatafrogOpt");
    env::set_var("POLONIUS_ALGORITHM", "Naive");

    args.push("-Zborrowck=mir".to_owned());
    args.push("-Zpolonius".to_owned());
    args.push("-Znll-facts".to_owned());
    args.push("-Zidentify-regions".to_owned());
    args.push("-Zdump-mir-dir=log/mir/".to_owned());
    args.push("-Zdump-mir=renumber".to_owned());

    if config::dump_debug_info() {
        args.push("-Zdump-mir=all".to_owned());
        args.push("-Zdump-mir-graphviz".to_owned());
    }

    // Hide confusing warnings
    args.push("-A".to_owned());
    args.push("unused_comparisons".to_owned());

    args.push("--cfg".to_string());
    args.push(r#"feature="prusti""#.to_string());

    if !config::contracts_lib().is_empty() {
        args.push("--extern".to_owned());
        args.push(format!("prusti_contracts={}", config::contracts_lib()));
    } else {
        warn!("Configuration variable CONTRACTS_LIB is empty");
    }

    let prusti_compiler_calls = Box::new(PrustiCompilerCalls::new());

    debug!("rustc command: '{}'", args.join(" "));
    rustc_driver::run_compiler(&args, prusti_compiler_calls, None, None)
}
