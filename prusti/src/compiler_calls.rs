// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use getopts;
use prusti_common::Stopwatch;
use prusti_interface;
use rustc::{self, session};
use rustc_codegen_utils::codegen_backend::CodegenBackend;
use rustc_driver::{driver, Compilation, CompilerCalls, RustcDefaultCalls};
use rustc_errors;
use std::{
    self,
    cell::Cell,
    path::PathBuf,
    rc::Rc,
    sync::{Arc, Mutex},
};
use syntax::ast;
use typeck;
use verifier;

use prusti_common::config;
use prusti_interface::trait_register::TraitRegister;

pub struct RegisterCalls {
    default: Box<RustcDefaultCalls>,
    register: Arc<Mutex<TraitRegister>>,
}

impl RegisterCalls {
    pub fn from_register(register: Arc<Mutex<TraitRegister>>) -> Self {
        Self {
            default: Box::new(RustcDefaultCalls),
            register: register,
        }
    }
}

impl<'a> CompilerCalls<'a> for RegisterCalls {
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
        self: Box<Self>,
        sess: &session::Session,
        matches: &getopts::Matches,
    ) -> driver::CompileController<'a> {
        let register = self.register.clone();
        let mut control = self.default.build_controller(sess, matches);

        // build register
        let old_after_parse_callback =
            std::mem::replace(&mut control.after_parse.callback, box |_| {});
        control.after_parse.callback = box move |state| {
            trace!("[after_parse.callback] enter");

            let stopwatch = Stopwatch::start("prusti", "trait register build");
            prusti_interface::parser::register_attributes(state);
            prusti_interface::parser::register_traits(state, register.clone());
            stopwatch.finish();

            trace!("[after_parse.callback] exit");
            old_after_parse_callback(state);
        };
        control.after_parse.stop = Compilation::Stop;

        control
    }
}

pub struct PrustiCompilerCalls {
    default: Box<RustcDefaultCalls>,
    register: Arc<Mutex<TraitRegister>>,
}

impl PrustiCompilerCalls {
    pub fn from_register(register: Arc<Mutex<TraitRegister>>) -> Self {
        Self {
            default: Box::new(RustcDefaultCalls),
            register: register,
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
        self: Box<Self>,
        sess: &session::Session,
        matches: &getopts::Matches,
    ) -> driver::CompileController<'a> {
        let register = self.register.clone();
        let mut control = self.default.build_controller(sess, matches);
        //control.make_glob_map = ???
        //control.keep_ast = true;

        let specifications = Rc::new(Cell::new(None));
        let put_specifications = Rc::clone(&specifications);
        let get_specifications = Rc::clone(&specifications);
        let old_after_parse_callback =
            std::mem::replace(&mut control.after_parse.callback, box |_| {});
        control.after_parse.callback = box move |state| {
            trace!("[after_parse.callback] enter");
            let stopwatch = Stopwatch::start("prusti", "annotation parsing");
            prusti_interface::parser::register_attributes(state);
            let untyped_specifications =
                prusti_interface::parser::rewrite_crate(state, register.clone());
            put_specifications.set(Some(untyped_specifications));
            stopwatch.finish();
            trace!("[after_parse.callback] exit");
            old_after_parse_callback(state);
        };

        let old_after_analysis_callback =
            std::mem::replace(&mut control.after_analysis.callback, box |_| {});
        control.after_analysis.callback = box move |state| {
            trace!("[after_analysis.callback] enter");

            let stopwatch = Stopwatch::start("prusti", "annotation type-checking");
            let untyped_specifications = get_specifications.replace(None).unwrap();
            let typed_specifications = typeck::type_specifications(state, untyped_specifications);
            debug!("typed_specifications = {:?}", typed_specifications);
            stopwatch.finish();

            // Call the verifier
            if !config::no_verify() {
                verifier::verify(state, typed_specifications);
            } else {
                warn!("Verification skipped due to the NO_VERIFY configuration flag.");
            }

            if config::full_compilation() {
                info!("Continue with compilation");
            }

            trace!("[after_analysis.callback] exit");
            old_after_analysis_callback(state);
        };

        if !config::full_compilation() {
            debug!("The program will not be compiled.");
            control.after_analysis.stop = Compilation::Stop;
        }
        control
    }
}
