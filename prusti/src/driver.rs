// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(box_syntax)]
#![feature(rustc_private)]

extern crate env_logger;
extern crate getopts;
#[macro_use]
extern crate log;
extern crate prusti;
extern crate rustc;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_codegen_utils;
extern crate syntax;
extern crate prusti_interface;
extern crate syntax_pos;

mod driver_utils;

use rustc::session;
use rustc_driver::{driver, Compilation, CompilerCalls, RustcDefaultCalls};
use rustc_codegen_utils::codegen_backend::CodegenBackend;
use std::env::{var, set_var};
use std::path::PathBuf;
use std::rc::Rc;
use std::cell::Cell;
use syntax::ast;
use syntax::feature_gate::AttributeType;
use prusti_interface::constants::PRUSTI_SPEC_ATTR;
use driver_utils::run;
use prusti_interface::config;

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
        control.after_parse.callback = Box::new(move |state| {
            trace!("[after_parse.callback] enter");
            {
                let registry = state.registry.as_mut().unwrap();
                registry.register_attribute(String::from("trusted"), AttributeType::Whitelisted);
                registry.register_attribute(String::from("pure"), AttributeType::Whitelisted);
                registry.register_attribute(String::from("invariant"), AttributeType::Whitelisted);
                registry.register_attribute(String::from("requires"), AttributeType::Whitelisted);
                registry.register_attribute(String::from("ensures"), AttributeType::Whitelisted);
                registry.register_attribute(
                    PRUSTI_SPEC_ATTR.to_string(),
                    AttributeType::Whitelisted
                );
                registry.register_attribute(
                    String::from("__PRUSTI_SPEC_ONLY"),
                    AttributeType::Whitelisted,
                );
                registry.register_attribute(
                    String::from("__PRUSTI_LOOP_SPEC_ID"),
                    AttributeType::Whitelisted,
                );
                registry.register_attribute(
                    String::from("__PRUSTI_EXPR_ID"),
                    AttributeType::Whitelisted,
                );
                registry.register_attribute(
                    String::from("__PRUSTI_FORALL_ID"),
                    AttributeType::Whitelisted,
                );
            }
            let untyped_specifications = prusti::parser::rewrite_crate(state);
            put_specifications.set(Some(untyped_specifications));

            info!("Parsing of annotations successful");

            trace!("[after_parse.callback] exit");
            old(state);
        });
        let old = std::mem::replace(&mut control.after_analysis.callback, box |_| {});
        control.after_analysis.callback = Box::new(move |state| {
            trace!("[after_analysis.callback] enter");
            let untyped_specifications = get_specifications.replace(None).unwrap();
            let typed_specifications =
                prusti::typeck::type_specifications(state, untyped_specifications);
            debug!("typed_specifications = {:?}", typed_specifications);

            info!("Type-checking of annotations successful");

            // Call the verifier
            if Ok(String::from("true")) != var("PRUSTI_NO_VERIFY") {
                prusti::verifier::verify(state, typed_specifications);
            } else {
                warn!("Verification skipped due to PRUSTI_NO_VERIFY env variable");
            }
            trace!("[after_analysis.callback] exit");
            old(state);
        });
        if Ok(String::from("true")) != var("PRUSTI_FULL_COMPILATION") {
            debug!("The program will not be compiled.");
            control.after_analysis.stop = Compilation::Stop;
        }
        control
    }
}

pub fn main() {
    env_logger::init();
    trace!("[main] enter");
    set_var("POLONIUS_ALGORITHM", "Naive");
    let mut args: Vec<String> = std::env::args().collect();
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
    /*
    if !config::contracts_lib().is_empty() {
        args.push("--extern".to_owned());
        args.push(format!("prusti_contracts={}", config::contracts_lib()));
    } else {
        warn!("Configuration variable CONTRACTS_LIB is empty");
    }
    */
    let args_string = args.join(" ");
    debug!("rustc command: {:?}", args_string);
    let prusti_compiler_calls = Box::new(PrustiCompilerCalls::new());
    let exit_status = run(move || rustc_driver::run_compiler(&args, prusti_compiler_calls, None, None));
    trace!("[main] exit");
    std::process::exit(exit_status as i32);
}
