#![feature(rustc_private)]
#![feature(proc_macro_internals)]

extern crate rustc_driver;

use log::debug;
use prusti::PrustiCompilerCalls;
use std::env;

/// Initialize Prusti and the Rust compiler loggers.
fn init_loggers() {
    let env = env_logger::Env::new()
        .filter("PRUSTI_LOG")
        .write_style("PRUSTI_LOG_STYLE");
    env_logger::init_from_env(env);
    rustc_driver::init_rustc_env_logger();
}

fn main() {
    rustc_driver::install_ice_hook();

    // If the environment asks us to actually be rustc, then do that.
    if env::var_os("PRUSTI_BE_RUSTC").is_some() {
        rustc_driver::main();
    }

    init_loggers();

    // We assume that prusti-rustc alread took care of the the compiler
    // arguments.
    let rustc_args: Vec<String> = env::args().collect();

    let mut args = Vec::new();
    let mut print_desugared_specs = false;
    let mut print_typeckd_specs = false;
    let mut verify = true;
    for arg in rustc_args {
        debug!("Arg: {}", arg);
        if arg == "-Zprint-desugared-specs" {
            print_desugared_specs = true;
        } else if arg == "-Zprint-typeckd-specs" {
            print_typeckd_specs = true;
        } else if arg == "-Zskip-verify" {
            verify = false;
        } else {
            args.push(arg);
        }
    }

    let mut callbacks = PrustiCompilerCalls {print_desugared_specs, print_typeckd_specs, verify};

    // Invoke compiler, and handle return code.
    let exit_code = rustc_driver::catch_with_exit_code(move || {
        rustc_driver::run_compiler(&args, &mut callbacks, None, None)
    });
    std::process::exit(exit_code)
}
