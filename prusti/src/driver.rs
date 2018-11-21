// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(box_syntax)]
#![feature(rustc_private)]

extern crate env_logger;
extern crate getopts;
#[macro_use]
extern crate log;
extern crate rustc;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_codegen_utils;
extern crate syntax;
extern crate prusti_interface;
extern crate syntax_pos;
extern crate prusti_viper;

mod driver_utils;
mod typeck;
mod verifier;

use rustc::session;
use rustc_driver::{driver, Compilation, CompilerCalls, RustcDefaultCalls};
use rustc_codegen_utils::codegen_backend::CodegenBackend;
use std::env;
use std::env::{var, set_var};
use std::path::PathBuf;
use std::rc::Rc;
use std::cell::Cell;
use syntax::ast;
use driver_utils::run;
use prusti_interface::config;
use prusti_interface::sysroot::current_sysroot;
use std::path::Path;
use std::time::Instant;

struct PrustiCompilerCalls {
    default: Box<RustcDefaultCalls>,
}

impl PrustiCompilerCalls {
    fn new() -> Self {
        Self {
            default: Box::new(RustcDefaultCalls),
        }
    }
}

impl<'a> CompilerCalls<'a> for PrustiCompilerCalls {
    fn early_callback(
        &mut self,
        matches: &getopts::Matches,
        sopts: &session::config::Options,
        cfg: &ast::CrateConfig,
        descriptions: &rustc_errors::registry::Registry,
        output: session::config::ErrorOutputType,
    ) -> Compilation {
        self.default
            .early_callback(matches, sopts, cfg, descriptions, output)
    }
    fn no_input(
        &mut self,
        matches: &getopts::Matches,
        sopts: &session::config::Options,
        cfg: &ast::CrateConfig,
        odir: &Option<PathBuf>,
        ofile: &Option<PathBuf>,
        descriptions: &rustc_errors::registry::Registry,
    ) -> Option<(session::config::Input, Option<PathBuf>)> {
        self.default
            .no_input(matches, sopts, cfg, odir, ofile, descriptions)
    }
    fn late_callback(
        &mut self,
        trans: &CodegenBackend,
        matches: &getopts::Matches,
        sess: &session::Session,
        crate_stores: &rustc::middle::cstore::CrateStore,
        input: &session::config::Input,
        odir: &Option<PathBuf>,
        ofile: &Option<PathBuf>,
    ) -> Compilation {
        if Ok(String::from("true")) == var("PRUSTI_TEST") {
            if let rustc::session::config::Input::File(ref path) = input {
                set_var("PRUSTI_TEST_FILE", path.to_str().unwrap());
            }
        }
        self.default
            .late_callback(trans, matches, sess, crate_stores, input, odir, ofile)
    }
    fn build_controller(
        self: Box<Self>,
        sess: &session::Session,
        matches: &getopts::Matches,
    ) -> driver::CompileController<'a> {
        let mut control = self.default.build_controller(sess, matches);
        //control.make_glob_map = ???
        //control.keep_ast = true;

        let old = std::mem::replace(&mut control.after_parse.callback, box |_| {});
        let specifications = Rc::new(Cell::new(None));
        let put_specifications = Rc::clone(&specifications);
        let get_specifications = Rc::clone(&specifications);
        control.after_parse.callback = box move |state| {
            trace!("[after_parse.callback] enter");
            let start = Instant::now();

            prusti_interface::parser::register_attributes(state);
            let untyped_specifications = prusti_interface::parser::rewrite_crate(state);
            put_specifications.set(Some(untyped_specifications));

            let duration = start.elapsed();
            info!("Parsing of annotations successful ({}.{} seconds)", duration.as_secs(), duration.subsec_millis()/10);
            trace!("[after_parse.callback] exit");
            old(state);
        };

        let old = std::mem::replace(&mut control.after_analysis.callback, box |_| {});
        control.after_analysis.callback = box move |state| {
            trace!("[after_analysis.callback] enter");
            let start = Instant::now();

            let untyped_specifications = get_specifications.replace(None).unwrap();
            let typed_specifications =
                typeck::type_specifications(state, untyped_specifications);
            debug!("typed_specifications = {:?}", typed_specifications);

            let duration = start.elapsed();
            info!("Type-checking of annotations successful ({}.{} seconds)", duration.as_secs(), duration.subsec_millis()/10);

            // Call the verifier
            if Ok(String::from("true")) != var("PRUSTI_NO_VERIFY") {
                verifier::verify(state, typed_specifications);
            } else {
                warn!("Verification skipped due to PRUSTI_NO_VERIFY env variable");
            }

            if Ok(String::from("true")) == var("PRUSTI_FULL_COMPILATION") {
                info!("Continue with compilation");
            }

            trace!("[after_analysis.callback] exit");
            old(state);
        };

        if Ok(String::from("true")) != var("PRUSTI_FULL_COMPILATION") {
            debug!("The program will not be compiled.");
            control.after_analysis.stop = Compilation::Stop;
        }
        control
    }
}

pub fn main() {
    env_logger::init();

    let exit_status = run(move || {
        let mut args: Vec<String> = env::args().collect();

        if args.len() <= 1 {
            std::process::exit(1);
        }

        // Disable Prusti if...
        let prusti_filter_disabled = true
            // we have been called by Cargo with RUSTC_WRAPPER, and
            && (args.len() > 1 && Path::new(&args[1]).file_stem() == Some("rustc".as_ref()))
            // this is not a test, and
            && !env::var("PRUSTI_TEST").ok().map_or(false, |val| val == "true")
            // this is not the final rustc invocation, thus we are compiling a dependency
            // See: https://github.com/rust-lang-nursery/rust-clippy/issues/1066#issuecomment-440393949
            && !args.iter().any(|s| s.starts_with("--emit=dep-info,metadata"));

        // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
        // We're invoking the compiler programmatically, so we ignore this
        if Path::new(&args[1]).file_stem() == Some("rustc".as_ref()) {
            args.remove(1);
        }

        // this conditional check for the --sysroot flag is there so users can call
        // `prusti-filter` directly without having to pass --sysroot or anything
        if !args.iter().any(|s| s == "--sysroot") {
            let sys_root = current_sysroot()
                .expect("need to specify SYSROOT env var during compilation, or use rustup or multirust");
            debug!("Using sys_root='{}'", sys_root);
            args.push("--sysroot".to_owned());
            args.push(sys_root);
        };

        // Early exit
        if prusti_filter_disabled {
            let default_compiler_calls = Box::new(RustcDefaultCalls);
            debug!("rustc command: '{}'", args.join(" "));
            return rustc_driver::run_compiler(&args, default_compiler_calls, None, None);
        }

        // Arguments required by Prusti (Rustc may produce different MIR)
        //set_var("POLONIUS_ALGORITHM", "DatafrogOpt"); TODO: Switch to opt because Naive does not
        // compute borrows.
        set_var("POLONIUS_ALGORITHM", "Naive");
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
    });
    std::process::exit(exit_status as i32);
}
