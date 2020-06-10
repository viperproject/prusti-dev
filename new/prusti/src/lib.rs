#![feature(rustc_private)]
#![feature(proc_macro_internals)]
#![feature(decl_macro)]
#![feature(box_syntax)]

extern crate proc_macro;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_expand;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_parse;
extern crate rustc_resolve;
extern crate rustc_session;
extern crate rustc_span;
extern crate smallvec;

use rustc_driver::Compilation;
use rustc_hir::intravisit;
use rustc_interface::interface::Compiler;
use rustc_interface::Queries;

mod specs;

pub struct PrustiCompilerCalls {
    /// Should Prusti print the AST with desugared specifications.
    print_desugared_specs: bool,
    /// Should Prusti print the type-checked specifications.
    print_typeckd_specs: bool,
}

impl PrustiCompilerCalls {
    pub fn new(print_desugared_specs: bool, print_typeckd_specs: bool) -> Self {
        Self {
            print_desugared_specs,
            print_typeckd_specs,
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
        let (krate, _resolver, _lint_store) = &mut *queries.expansion().unwrap().peek_mut();
        if self.print_desugared_specs {
            rustc_driver::pretty::print_after_parsing(
                compiler.session(),
                compiler.input(),
                krate,
                rustc_session::config::PpMode::PpmSource(
                    rustc_session::config::PpSourceMode::PpmNormal,
                ),
                None,
            );
        }
        Compilation::Continue
    }
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let hir = tcx.hir();
            let krate = hir.krate();
            let mut visitor = specs::SpecCollector::new(tcx);
            intravisit::walk_crate(&mut visitor, &krate);
            let type_map = visitor.determine_typed_procedure_specs();
            if self.print_typeckd_specs {
                let mut sorted_def_ids: Vec<_> = type_map.keys().cloned().collect();
                sorted_def_ids.sort();
                for def_id in sorted_def_ids {
                    println!("{:?} {:?}", def_id, type_map[&def_id]);
                }
            }
        });

        compiler.session().abort_if_errors();
        Compilation::Stop
    }
}
