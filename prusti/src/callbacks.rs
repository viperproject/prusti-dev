use prusti_interface::{specs, environment::Environment};
use prusti_common::config::ConfigFlags;
use rustc_driver::Compilation;
use rustc_hir::intravisit;
use rustc_interface::interface::Compiler;
use rustc_interface::Queries;
use regex::Regex;
use prusti_common::config;
use crate::verifier::verify;

pub struct PrustiCompilerCalls {
    flags: ConfigFlags,
}

impl PrustiCompilerCalls {
    pub fn new(flags: ConfigFlags) -> Self {
        Self { flags }
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
        if self.flags.print_desugared_specs {
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
            let env = Environment::new(tcx);
            let def_spec = visitor.determine_def_specs(&env);
            /*
            let type_map = visitor.determine_typed_procedure_specs();
            if self.flags.print_typeckd_specs {
                let mut values: Vec<_> = type_map
                    .values()
                    .map(|spec| format!("{:?}", spec))
                    .collect();
                if self.flags.hide_uuids {
                    let uuid = Regex::new(
                        "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}"
                    ).unwrap();
                    let num_uuid = Regex::new("[a-z0-9]{32}").unwrap();
                    let mut replaced_values: Vec<String> = vec![];
                    for item in values {
                        let item = num_uuid.replace_all(&item, "$(NUM_UUID)");
                        let item = uuid.replace_all(&item, "$(UUID)");
                        replaced_values.push(String::from(item));
                    }
                    values = replaced_values;
                }
                // We sort in this strange way so that the output is
                // determinstic enough to be used in tests.
                values.sort_by_key(|v| (v.len(), v.to_string()));
                for value in values {
                    println!("{}", value);
                }
            }
            */
            if !self.flags.skip_verify {
                verify(self.flags, env, def_spec);
            }
        });

        compiler.session().abort_if_errors();
        if config::full_compilation() {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}
