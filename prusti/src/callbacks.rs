use crate::verifier::verify;
use prusti_common::config;
use prusti_interface::{
    environment::{mir_storage, Environment},
    specs,
};
use prusti_rustc_interface::{
    driver::Compilation,
    hir::def_id::LocalDefId,
    interface::{interface::Compiler, Config, Queries},
    middle::ty::{
        self,
        query::{query_values::mir_borrowck, ExternProviders, Providers},
        TyCtxt,
    },
    session::Session,
};
use regex::Regex;

#[derive(Default)]
pub struct PrustiCompilerCalls;

#[allow(clippy::needless_lifetimes)]
fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> mir_borrowck<'tcx> {
    let body_with_facts = prusti_rustc_interface::borrowck::consumers::get_body_with_borrowck_facts(
        tcx,
        ty::WithOptConstParam::unknown(def_id),
    );
    // SAFETY: This is safe because we are feeding in the same `tcx` that is
    // going to be used as a witness when pulling out the data.
    unsafe {
        mir_storage::store_mir_body(tcx, def_id, body_with_facts);
    }
    let mut providers = Providers::default();
    prusti_rustc_interface::borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

fn override_queries(_session: &Session, local: &mut Providers, _external: &mut ExternProviders) {
    local.mir_borrowck = mir_borrowck;
}

impl prusti_rustc_interface::driver::Callbacks for PrustiCompilerCalls {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(override_queries);
    }
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();
        let (krate, _resolver, _lint_store) = &mut *queries.expansion().unwrap().peek_mut();
        if config::print_desugared_specs() {
            prusti_rustc_interface::driver::pretty::print_after_parsing(
                compiler.session(),
                compiler.input(),
                krate,
                prusti_rustc_interface::session::config::PpMode::Source(
                    prusti_rustc_interface::session::config::PpSourceMode::Normal,
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
            let env = Environment::new(tcx);
            let spec_checker = specs::checker::SpecChecker::new();
            spec_checker.check(&env);
            compiler.session().abort_if_errors();

            let mut spec_collector = specs::SpecCollector::new(&env);
            tcx.hir().walk_toplevel_module(&mut spec_collector);
            tcx.hir().walk_attributes(&mut spec_collector);
            let def_spec = spec_collector.build_def_specs();
            if config::print_typeckd_specs() {
                let loop_specs: Vec<_> = def_spec
                    .loop_specs
                    .values()
                    .map(|spec| format!("{:?}", spec))
                    .collect();
                let proc_specs: Vec<_> = def_spec
                    .proc_specs
                    .values()
                    .map(|spec| format!("{:?}", spec.base_spec))
                    .collect();
                let type_specs: Vec<_> = def_spec
                    .type_specs
                    .values()
                    .map(|spec| format!("{:?}", spec))
                    .collect();
                let asserts: Vec<_> = def_spec
                    .prusti_assertions
                    .values()
                    .map(|spec| format!("{:?}", spec))
                    .collect();
                let assumptions: Vec<_> = def_spec
                    .prusti_assumptions
                    .values()
                    .map(|spec| format!("{:?}", spec))
                    .collect();
                let mut values = Vec::new();
                values.extend(loop_specs);
                values.extend(proc_specs);
                values.extend(type_specs);
                values.extend(asserts);
                values.extend(assumptions);
                if config::hide_uuids() {
                    let uuid =
                        Regex::new("[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}")
                            .unwrap();
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
            if !config::no_verify() {
                verify(env, def_spec);
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
