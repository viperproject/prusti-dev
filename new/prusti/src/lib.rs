#![feature(rustc_private)]
#![feature(proc_macro_internals)]

extern crate proc_macro;
extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_expand;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_resolve;

use rustc_driver::Compilation;
use rustc_interface::interface::Compiler;
use rustc_interface::Queries;
use std::path::PathBuf;

mod specs;

pub struct PrustiCompilerCalls {
    /// Path to the `.so` file containing the `prusti_contracts_internal` crate.
    prusti_contracts_internal_path: PathBuf,
}

impl PrustiCompilerCalls {
    pub fn new(prusti_contracts_internal_path: PathBuf) -> Self {
        Self {
            prusti_contracts_internal_path,
        }
    }
}

impl rustc_driver::Callbacks for PrustiCompilerCalls {
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();
        let (krate, resolver, _lint_store) = &mut *queries.expansion().unwrap().peek_mut();
        let result = resolver.borrow().borrow_mut().access(|resolver| {
            specs::rewrite_crate(
                compiler,
                resolver,
                krate,
                &self.prusti_contracts_internal_path,
            )
        });
        if result.is_err() {
            Compilation::Stop
        } else {
            Compilation::Continue
        }
    }
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        _queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();
        Compilation::Stop
    }
}
