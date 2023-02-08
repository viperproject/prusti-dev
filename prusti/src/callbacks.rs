use crate::{
    ide_helper::{fake_error::fake_error, compiler_info},
    verifier::verify,
};
use prusti_common::config;
use prusti_interface::{
    data::VerificationTask,
    environment::{mir_storage, Environment},
    specs::{self, cross_crate::CrossCrateSpecs, is_spec_fn},
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

#[derive(Default)]
pub struct PrustiCompilerCalls;

// Running `get_body_with_borrowck_facts` can be very slow, therefore we avoid it when not
// necessary; for crates which won't be verified or spec_fns it suffices to load just the fn body

#[allow(clippy::needless_lifetimes)]
fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> mir_borrowck<'tcx> {
    // *Don't take MIR bodies with borrowck info if we won't need them*
    if !is_spec_fn(tcx, def_id.to_def_id()) {
        let body_with_facts =
            prusti_rustc_interface::borrowck::consumers::get_body_with_borrowck_facts(
                tcx,
                ty::WithOptConstParam::unknown(def_id),
            );
        // SAFETY: This is safe because we are feeding in the same `tcx` that is
        // going to be used as a witness when pulling out the data.
        unsafe {
            mir_storage::store_mir_body(tcx, def_id, body_with_facts);
        }
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
        // *Don't take MIR bodies with borrowck info if we won't need them*
        if !config::no_verify() {
            assert!(config.override_queries.is_none());
            config.override_queries = Some(override_queries);
        }
    }
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        if compiler.session().rust_2015() {
            compiler
                .session()
                .struct_warn(
                    "Prusti specifications are supported only from 2018 edition. Please \
                 specify the edition with adding a command line argument `--edition=2018` or \
                 `--edition=2021`.",
                )
                .emit();
        }
        compiler.session().abort_if_errors();
        let mut expansion_result = queries.expansion().unwrap();
        let (krate, _resolver, _lint_store) = expansion_result.get_mut();
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
        queries.global_ctxt().unwrap().enter(|tcx| {
            let mut env = Environment::new(tcx, env!("CARGO_PKG_VERSION"));
            let spec_checker = specs::checker::SpecChecker::new();
            spec_checker.check(&env);
            compiler.session().abort_if_errors();

            let hir = env.query.hir();
            let mut spec_collector = specs::SpecCollector::new(&mut env);
            hir.walk_toplevel_module(&mut spec_collector);
            hir.walk_attributes(&mut spec_collector);

            let mut def_spec = spec_collector.build_def_specs();
            // Do print_typeckd_specs prior to importing cross crate
            if config::print_typeckd_specs() {
                for value in def_spec.all_values_debug(config::hide_uuids()) {
                    println!("{value}");
                }
            }
            CrossCrateSpecs::import_export_cross_crate(&mut env, &mut def_spec);

            // determine procedures that have to be verified.
            let (annotated_procedures, types) = env.get_annotated_procedures_and_types();

            // todo: selective verification, filter procedures that are
            // part of verification_task

            if config::show_ide_info() && !config::no_verify() {
                let compiler_info = compiler_info::IdeInfo::collect(&env, &annotated_procedures);
                let out = serde_json::to_string(&compiler_info).unwrap();
                // probably should make this part of compilers output..
                // actually not sure which way is better...
                println!("{}", out);
            }

            // collect and output Information used by IDE:

            if !config::no_verify() && !config::skip_verification() {
                if config::selective_verify().is_none() {
                    println!("verifying everything\n\n\n");
                    let verification_task = VerificationTask {
                        procedures: annotated_procedures,
                        types,
                    };
                    verify(env, def_spec, verification_task);
                } else {
                    let target_def_path = config::selective_verify().unwrap();
                    println!(
                        "Selective Verification invoked for method {}\n\n\n",
                        target_def_path
                    );
                    let procedures = annotated_procedures
                        .into_iter()
                        .filter(|x| env.name.get_item_def_path(*x) == target_def_path)
                        .collect();
                    let selective_task = VerificationTask { procedures, types };
                    verify(env, def_spec, selective_task);
                }
            } else if config::show_ide_info() && config::skip_verification() && !config::no_verify()
            {
                // add a fake error
                // for now maybe only for our use-case
                // This stops cargo-prusti from successfully verifying crates
                // it should not be able to after this invocation
                fake_error(env)
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
