use crate::{
    ide_helper::{compiler_info, fake_error::fake_error},
    verifier::verify,
};
use prusti_common::config;
use prusti_interface::{
    data::VerificationTask,
    environment::{mir_storage, Environment},
    specs::{self, cross_crate::CrossCrateSpecs, is_spec_fn},
    PrustiError,
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
    span::DUMMY_SP,
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

impl prusti_rustc_interface::driver::Callbacks for PrustiCompilerCalls {
    fn config(&mut self, config: &mut Config) {
        // *Don't take MIR bodies with borrowck info if we won't need them*
        if !config::no_verify() {
            assert!(config.override_queries.is_none());
            config.override_queries = Some(
                |_session: &Session, providers: &mut Providers, _external: &mut ExternProviders| {
                    providers.mir_borrowck = mir_borrowck;
                },
            );
        }
    }
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        if compiler.session().is_rust_2015() {
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
        if config::print_desugared_specs() {
            // based on the implementation of rustc_driver::pretty::print_after_parsing
            queries.global_ctxt().unwrap().enter(|tcx| {
                let sess = compiler.session();
                let krate = &tcx.resolver_for_lowering(()).borrow().1;
                let src_name = sess.io.input.source_name();
                let src = sess
                    .source_map()
                    .get_source_file(&src_name)
                    .expect("get_source_file")
                    .src
                    .as_ref()
                    .expect("src")
                    .to_string();
                print!(
                    "{}",
                    prusti_rustc_interface::ast_pretty::pprust::print_crate(
                        sess.source_map(),
                        krate,
                        src_name,
                        src,
                        &prusti_rustc_interface::ast_pretty::pprust::state::NoAnn,
                        false,
                        sess.edition(),
                        &sess.parse_sess.attr_id_generator,
                    )
                );
            });
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

            // TODO: can we replace `get_annotated_procedures` with information
            // that is already in `def_spec`?
            let (annotated_procedures, types) = env.get_annotated_procedures_and_types();

            if config::show_ide_info() && !config::no_verify() {
                let compiler_info =
                    compiler_info::IdeInfo::collect(&env, &annotated_procedures, &def_spec);
                let out = serde_json::to_string(&compiler_info).unwrap();
                PrustiError::message(format!("compilerInfo{out}"), DUMMY_SP.into())
                    .emit(&env.diagnostic);
            }

            // collect and output Information used by IDE:
            if !config::no_verify() && !config::skip_verification() {
                if let Some(target_def_path) = config::verify_only_defpath() {
                    let procedures = annotated_procedures
                        .into_iter()
                        .filter(|x| env.name.get_unique_item_name(*x) == target_def_path)
                        .collect();
                    let selective_task = VerificationTask { procedures, types };
                    // fake_error because otherwise a verification-success
                    // (for a single method for example) will cause this result
                    // to be cached by compiler at the moment
                    verify(&env, def_spec, selective_task);
                    fake_error(&env);
                } else {
                    let verification_task = VerificationTask {
                        procedures: annotated_procedures,
                        types,
                    };
                    verify(&env, def_spec, verification_task);
                }
            } else if config::skip_verification() && !config::no_verify() {
                // add a fake error, reason explained in issue #1261
                fake_error(&env)
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
