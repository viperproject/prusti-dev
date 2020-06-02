// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use getopts;
use rustc;
use rustc::session;
use rustc_codegen_utils::codegen_backend::CodegenBackend;
use rustc_driver::{driver, Compilation, CompilerCalls, RustcDefaultCalls};
use rustc_errors;
use std;
use std::path::PathBuf;
use std::rc::Rc;
use std::cell::RefCell;
use std::time::Instant;
use syntax::ast;
use prusti_interface;
use prusti_interface::trait_register::TraitRegister;

pub struct RegisterCalls {
    default: Box<RustcDefaultCalls>,
    trait_register: Rc<RefCell<TraitRegister>>,
}

impl RegisterCalls {
    pub fn from_register(register: Rc<RefCell<TraitRegister>>) -> Self {
        Self {
            default: Box::new(RustcDefaultCalls),
            trait_register: register,
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
        let register = self.trait_register.clone();
        let mut control = self.default.build_controller(sess, matches);
        
        // build register
        let old_after_parse_callback =
            std::mem::replace(&mut control.after_parse.callback, box |_| {});
        control.after_parse.callback = box move |state| {
            trace!("[after_parse.callback first_pass] enter");
            let start = Instant::now();

            prusti_interface::parser::register_attributes(state);
            prusti_interface::parser::register_traits(state, register.clone());

            let duration = start.elapsed();
            info!(
                "Trait register build successful ({}.{} seconds)",
                duration.as_secs(),
                duration.subsec_millis() / 10
            );
            trace!("[after_parse.callback first_pass] exit");
            old_after_parse_callback(state);
        };
        // stop compilation
        control.after_parse.stop = Compilation::Stop;
        control
    }
}
