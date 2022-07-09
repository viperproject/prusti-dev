// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]
#![feature(proc_macro_internals)]
#![feature(decl_macro)]
#![feature(box_syntax)]
#![deny(unused_must_use)]

mod arg_value;
mod callbacks;
mod verifier;

use arg_value::arg_value;
use callbacks::PrustiCompilerCalls;
use lazy_static::lazy_static;
use log::{info, warn};
use prusti_common::{config, report::user, Stopwatch};
use prusti_rustc_interface::interface::interface::try_print_query_stack;
use std::{borrow::Cow, env, panic};

/// Link to report Prusti bugs
const BUG_REPORT_URL: &str = "https://github.com/viperproject/prusti-dev/issues/new";

lazy_static! {
    static ref ICE_HOOK: Box<dyn Fn(&panic::PanicInfo<'_>) + Sync + Send + 'static> = {
        let hook = panic::take_hook();
        panic::set_hook(box |info| report_prusti_ice(info, BUG_REPORT_URL));
        hook
    };
}

fn get_prusti_version_info() -> String {
    format!(
        "commit {} {}, built on {}",
        option_env!("COMMIT_HASH").unwrap_or("<unknown>"),
        option_env!("COMMIT_TIME").unwrap_or("<unknown>"),
        option_env!("BUILD_TIME").unwrap_or("<unknown>"),
    )
}

/// Report a readable error message in case of panic, with a link to open a new Prusti issue.
fn report_prusti_ice(info: &panic::PanicInfo<'_>, bug_report_url: &str) {
    // Invoke our ICE handler, which prints the actual panic message and optionally a backtrace
    (*ICE_HOOK)(info);

    // Separate the output with an empty line
    eprintln!();

    let fallback_bundle = prusti_rustc_interface::errors::fallback_fluent_bundle(
        prusti_rustc_interface::errors::DEFAULT_LOCALE_RESOURCES,
        false,
    );
    let emitter = box prusti_rustc_interface::errors::emitter::EmitterWriter::stderr(
        prusti_rustc_interface::errors::ColorConfig::Auto,
        None,
        None,
        fallback_bundle,
        false,
        false,
        None,
        false,
    );
    let handler = prusti_rustc_interface::errors::Handler::with_emitter(true, None, emitter);

    // a .span_bug or .bug call has already printed what it wants to print.
    if !info
        .payload()
        .is::<prusti_rustc_interface::errors::ExplicitBug>()
    {
        let mut d = prusti_rustc_interface::errors::Diagnostic::new(
            prusti_rustc_interface::errors::Level::Bug,
            "unexpected panic",
        );
        handler.emit_diagnostic(&mut d);
    }

    let version_info = get_prusti_version_info();

    let xs: Vec<Cow<'static, str>> = vec![
        "Prusti or the compiler unexpectedly panicked. This is a bug.".into(),
        format!("We would appreciate a bug report: {}", bug_report_url).into(),
        format!("Prusti version: {}", version_info).into(),
    ];

    for note in &xs {
        handler.note_without_error(note.as_ref());
    }

    // If backtraces are enabled, also print the query stack
    let backtrace = env::var_os("RUST_BACKTRACE").map_or(false, |x| &x != "0");

    if backtrace {
        try_print_query_stack(&handler, None);
    }
}

/// Initialize Prusti and the Rust compiler loggers.
fn init_loggers() {
    let env = env_logger::Env::new()
        .filter("PRUSTI_LOG")
        .write_style("PRUSTI_LOG_STYLE");
    env_logger::init_from_env(env);
    prusti_rustc_interface::driver::init_rustc_env_logger();
}

const PRUSTI_PACKAGES: [&str; 4] = [
    "prusti-contracts-internal",
    "prusti-contracts-impl",
    "prusti-contracts",
    "prusti-specs",
];

fn main() {
    let stopwatch = Stopwatch::start("prusti", "main");

    // We assume that prusti-rustc already removed the first "rustc" argument
    // added by RUSTC_WRAPPER and all command line arguments -P<arg>=<val>
    // have been filtered out.
    let original_rustc_args = config::get_filtered_args();

    // If the environment asks us to actually be rustc, or if lints have been disabled (which
    // indicates that an upstream dependency is being compiled), then run `rustc` instead of Prusti.
    let prusti_be_rustc = config::be_rustc();
    // This environment variable will not be set when building dependencies.
    let is_primary_package = env::var("CARGO_PRIMARY_PACKAGE").is_ok();
    let is_no_verify_crate = !is_primary_package && config::no_verify_deps();
    let are_lints_disabled =
        arg_value(&original_rustc_args, "--cap-lints", |val| val == "allow").is_some();
    let is_prusti_package = env::var("CARGO_PKG_NAME")
        .map(|name| PRUSTI_PACKAGES.contains(&name.as_str()))
        .unwrap_or(false);
    if prusti_be_rustc || is_no_verify_crate || are_lints_disabled || is_prusti_package {
        prusti_rustc_interface::driver::main();
    }

    lazy_static::initialize(&ICE_HOOK);
    init_loggers();

    // Disable incremental compilation because it causes mir_borrowck not to
    // be called.
    let mut rustc_args = Vec::new();
    let mut is_codegen = false;
    let mut contains_edition = false;
    let mut only_print = false;
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
            if arg == "--edition=2018" || arg == "--edition=2021" {
                contains_edition = true;
            }
            if arg.starts_with("--print=") {
                only_print = true;
            }
            rustc_args.push(arg);
        }
    }
    if !contains_edition && !only_print {
        warn!(
            "Specifications are supported only from 2018 edition. Please specify \
               the edition with adding a command line argument `--edition=2018` or \
               `--edition=2021`."
        );
    }

    let exit_code = prusti_rustc_interface::driver::catch_with_exit_code(move || {
        user::message(format!(
            "{}\n{}\n{}\n",
            r"  __          __        __  ___             ",
            r" |__)  _\/_  |__) |  | /__`  |   ____\/_  | ",
            r" |      /\   |  \ \__/ .__/  |       /\   | ",
        ));
        user::message(format!("Prusti version: {}", get_prusti_version_info()));
        info!("Prusti version: {}", get_prusti_version_info());

        rustc_args.push("-Zpolonius".to_owned());
        rustc_args.push("-Zalways-encode-mir".to_owned());
        rustc_args.push("-Zcrate-attr=feature(type_ascription)".to_owned());
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

        let mut callbacks = PrustiCompilerCalls::default();

        prusti_rustc_interface::driver::RunCompiler::new(&rustc_args, &mut callbacks).run()
    });
    let duration = stopwatch.finish();
    if let Some(deadline) = config::verification_deadline() {
        // Check that we met the deadline.
        assert!(
            duration < std::time::Duration::from_secs(deadline),
            "Prusti failed to finish within {} seconds. It finished in {:?}.",
            deadline,
            duration,
        );
    }
    std::process::exit(exit_code)
}
