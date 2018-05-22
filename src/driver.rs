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

use rustc::session;
use rustc_driver::{driver, Compilation, CompilerCalls, RustcDefaultCalls};
use rustc_codegen_utils::codegen_backend::CodegenBackend;
use std::env::var;
use std::path::PathBuf;
use std::process::Command;
use std::rc::Rc;
use std::cell::Cell;
use syntax::ast;
use syntax::feature_gate::AttributeType;

struct PrustiCompilerCalls {
    default: RustcDefaultCalls,
}

impl PrustiCompilerCalls {
    fn new() -> Self {
        Self {
            default: RustcDefaultCalls,
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
        self.default
            .late_callback(trans, matches, sess, crate_stores, input, odir, ofile)
    }
    fn build_controller(
        &mut self,
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
                registry.register_attribute(String::from("invariant"), AttributeType::Whitelisted);
                registry.register_attribute(String::from("requires"), AttributeType::Whitelisted);
                registry.register_attribute(String::from("ensures"), AttributeType::Whitelisted);
                registry
                    .register_attribute(String::from("__PRUSTI_SPEC"), AttributeType::Whitelisted);
                registry.register_attribute(
                    String::from("__PRUSTI_SPEC_ONLY"),
                    AttributeType::Whitelisted,
                );
            }
            let untyped_specifications = prusti::parser::rewrite_crate(state);
            put_specifications.set(Some(untyped_specifications));

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
            // Call the verifier
            if Ok(String::from("true")) != var("PRUSTI_NO_VERIFY") {
                prusti::verifier::verify(state, typed_specifications);
            } else {
                warn!("Verification skipped due to PRUSTI_NO_VERIFY env variable");
            }
            trace!("[after_analysis.callback] exit");
            old(state);
        });
        if Ok(String::from("true")) != var("PRUSTI_TESTS") {
            control.after_analysis.stop = Compilation::Stop;
        }
        control
    }
}

#[allow(dead_code)]
fn get_sysroot() -> String {
    Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .map(|s| s.trim().to_owned())
        .expect("Failed to figure out SYSROOT.")
}

pub fn main() {
    env_logger::init().unwrap();
    trace!("[main] enter");
    let args: Vec<String> = std::env::args().collect();
    //args.push("--sysroot".to_owned());
    //args.push(get_sysroot());
    let mut prusti_compiler_calls = PrustiCompilerCalls::new();
    rustc_driver::in_rustc_thread(move || {
        let (result, _) = rustc_driver::run_compiler(&args, &mut prusti_compiler_calls, None, None);
        if let Err(session::CompileIncomplete::Errored(_)) = result {
            std::process::exit(101);
        }
    }).expect("rustc_thread failed");
    trace!("[main] exit");
}
