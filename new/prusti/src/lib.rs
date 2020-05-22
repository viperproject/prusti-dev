#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_resolve;

use rustc_driver::Compilation;

mod specs;

pub struct PrustiCompilerCalls {}

impl rustc_driver::Callbacks for PrustiCompilerCalls {
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();
        let (krate, resolver, _lint_store) = &mut *queries.expansion().unwrap().peek_mut();
        resolver.borrow().borrow_mut().access(|resolver| {
            specs::rewrite_crate(krate, resolver);
        });
        Compilation::Continue
    }
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        _queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();
        Compilation::Stop
    }
}
