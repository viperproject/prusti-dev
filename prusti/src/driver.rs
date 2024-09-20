// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]
#![feature(proc_macro_internals)]
#![feature(decl_macro)]
#![deny(unused_must_use)]

mod arg_value;
mod callbacks;
mod verifier;

use arg_value::arg_value;
use callbacks::PrustiCompilerCalls;
use log::info;
use prusti_utils::{config, report::user, Stopwatch};
use prusti_rustc_interface::{
    driver, errors,
    session::{self, EarlyDiagCtxt},
};
use std::env;
use tracing_chrome::{ChromeLayerBuilder, FlushGuard};
use tracing_subscriber::{filter::EnvFilter, prelude::*};

/// Link to report Prusti bugs
const BUG_REPORT_URL: &str = "https://github.com/viperproject/prusti-dev/issues/new";

fn get_prusti_version_info() -> String {
    format!(
        "{}, commit {} {}, built on {}",
        env!("CARGO_PKG_VERSION"),
        option_env!("COMMIT_HASH").unwrap_or("<unknown>"),
        option_env!("COMMIT_TIME").unwrap_or("<unknown>"),
        option_env!("BUILD_TIME").unwrap_or("<unknown>"),
    )
}

/// Initialize Prusti and the Rust compiler loggers.
fn init_loggers() -> Option<FlushGuard> {
    // TODO: The `config::log() != ""` here is very bad; it makes us ignore the `log_tracing` flag
    // It's enabled so that we only create a `trace.json` file if the user has explicitly requested logging
    let guard = if config::log_tracing() && !config::log().is_empty() {
        let log_dir = config::log_dir();
        std::fs::create_dir_all(&log_dir).expect("failed to create log directory");
        let filter = EnvFilter::new(config::log());
        let (chrome_layer, guard) = ChromeLayerBuilder::new()
            .file(log_dir.join("trace.json"))
            .include_args(true)
            .build();
        tracing_subscriber::registry()
            .with(filter)
            .with(chrome_layer)
            .init();
        Some(guard)
    } else {
        env_logger::init_from_env(
            env_logger::Env::new()
                .filter_or("PRUSTI_LOG", config::log())
                .write_style_or("PRUSTI_LOG_STYLE", config::log_style()),
        );
        None
    };

    let error_handler = EarlyDiagCtxt::new(session::config::ErrorOutputType::default());
    prusti_rustc_interface::driver::init_rustc_env_logger(&error_handler);
    guard
}

fn main() {
    driver::install_ice_hook(BUG_REPORT_URL, |handler| {
        let version_info = get_prusti_version_info();
        handler.handle().note(format!("Prusti version: {version_info}"));
    });

    // To measure how long Prusti takes to run
    let stopwatch = Stopwatch::start("prusti", "main");

    // Filter out Prusti's `-P<arg>=<val>` arguments
    let original_rustc_args = config::get_filtered_args();

    // If the environment asks us to actually be rustc, then run `rustc` instead of Prusti,
    // or if we're building a build script where we can't retrieve MIR bodies.
    let build_script_build = arg_value(&original_rustc_args, "--crate-name", |val| {
        val == "build_script_build"
    })
    .is_some();
    if config::be_rustc() || build_script_build {
        driver::main();
    }

    // Initialize Prusti and the Rust compiler loggers.
    // This must be done after the build script check, otherwise Tokio's global tracing will fail.
    let _log_flush_guard = init_loggers();

    // This environment variable will not be set when building dependencies.
    let is_primary_package = env::var("CARGO_PRIMARY_PACKAGE").is_ok();
    // Is this crate a dependency when user doesn't want to verify dependencies
    let is_no_verify_dep_crate = !is_primary_package && config::no_verify_deps();

    // Would `cargo check` not report errors for this crate? That is, are lints disabled
    // (i.e. is this a non-local crate)
    let are_lints_disabled =
        arg_value(&original_rustc_args, "--cap-lints", |val| val == "allow").is_some();

    // Remote dependencies (e.g. from git/crates.io), or any dependencies if `no_verify_deps`,
    // are not verified. However, we still run Prusti on them to export potential specs.
    if is_no_verify_dep_crate || are_lints_disabled {
        config::set_no_verify(true);
    }

    // Disable incremental compilation because it causes mir_borrowck not to be called.
    let mut rustc_args = Vec::new();
    let mut is_codegen = false;
    for arg in original_rustc_args {
        if arg == "--codegen" || arg == "-C" {
            is_codegen = true;
        } else if is_codegen && arg.starts_with("incremental=") {
            // Just drop the argument.
            is_codegen = false;
        } else {
            if is_codegen {
                rustc_args.push("-C".to_owned());
                is_codegen = false;
            }
            rustc_args.push(arg);
        }
    }

    let exit_code = driver::catch_with_exit_code(move || {
        user::message(format!(
            "{}\n{}\n{}\n",
            r"  __          __        __  ___             ",
            r" |__)  _\/_  |__) |  | /__`  |   ____\/_  | ",
            r" |      /\   |  \ \__/ .__/  |       /\   | ",
        ));
        user::message(format!("Prusti version: {}", get_prusti_version_info()));
        info!("Prusti version: {}", get_prusti_version_info());

        if rustc_args.get(1).map(|s| s.as_ref()) == Some("-vV") {
            // When cargo queries the verbose rustc version,
            // also print the Prusti version to stdout.
            // This ensures that the cargo build cache is
            // invalidated when the Prusti version changes.
            println!("Prusti version: {}", get_prusti_version_info());
        }

        rustc_args.push("-Zalways-encode-mir".to_owned());
        rustc_args.push("-Zcrate-attr=feature(stmt_expr_attributes)".to_owned());
        rustc_args.push("-Zcrate-attr=feature(register_tool)".to_owned());
        rustc_args.push("-Zcrate-attr=register_tool(prusti)".to_owned());

        if config::check_overflows() {
            // Some crates might have a `overflow-checks = false` in their `Cargo.toml` to
            // disable integer overflow checks, but we want to override that.
            rustc_args.push("-Coverflow-checks=on".to_owned());
        }

        if config::dump_debug_info() {
            rustc_args.push(format!(
                "-Zdump-mir-dir={}",
                config::log_dir()
                    .join("mir")
                    .to_str()
                    .expect("failed to configure dump-mir-dir")
            ));
            rustc_args.push("-Zdump-mir=all".to_owned());
            rustc_args.push("-Zdump-mir-graphviz".to_owned());
            if !config::ignore_regions() {
                rustc_args.push("-Zidentify-regions=yes".to_owned());
            }
        }
        if config::dump_nll_facts() {
            rustc_args.push("-Znll-facts=yes".to_string());
            rustc_args.push(format!(
                "-Znll-facts-dir={}",
                config::log_dir()
                    .join("nll-facts")
                    .to_str()
                    .expect("failed to configure nll-facts-dir")
            ));
        }

        let mut callbacks = PrustiCompilerCalls;

        driver::RunCompiler::new(&rustc_args, &mut callbacks).run()
    });

    // Check if verifying a program in our test suite is taking too long
    let duration = stopwatch.finish();
    if let Some(deadline) = config::verification_deadline() {
        // Check that we met the deadline.
        assert!(
            duration < std::time::Duration::from_secs(deadline),
            "Prusti failed to finish within {deadline} seconds. It finished in {duration:?}.",
        );
    }

    std::process::exit(exit_code)
}
