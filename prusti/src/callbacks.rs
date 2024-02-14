use crate::verifier::verify;
use mir_state_analysis::{test_coupling_graph, test_free_pcs};
use prusti_common::config;
use prusti_interface::{
    environment::{mir_storage, Environment},
    specs::{self, cross_crate::CrossCrateSpecs, is_spec_fn},
};
use prusti_rustc_interface::{
    borrowck::consumers,
    data_structures::steal::Steal,
    driver::Compilation,
    hir::{def::DefKind, def_id::LocalDefId},
    index::IndexVec,
    interface::{interface::Compiler, Config, Queries},
    middle::{
        mir::{self, BorrowCheckResult},
        query::{ExternProviders, Providers},
        ty::TyCtxt,
    },
    session::Session,
};

#[derive(Default)]
pub struct PrustiCompilerCalls;

// Running `get_body_with_borrowck_facts` can be very slow, therefore we avoid it when not
// necessary; for crates which won't be verified or spec_fns it suffices to load just the fn body

#[allow(clippy::needless_lifetimes)]
#[tracing::instrument(level = "debug", skip(tcx))]
fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> &BorrowCheckResult<'tcx> {
    let def_kind = tcx.def_kind(def_id.to_def_id());
    let is_anon_const = matches!(def_kind, DefKind::AnonConst);
    // Anon Const bodies have already been stolen and so will result in a crash
    // when calling `get_body_with_borrowck_facts`. TODO: figure out if we need
    // (anon) const bodies at all, and if so, how to get them?
    if !is_anon_const {
        let consumer_opts = if is_spec_fn(tcx, def_id.to_def_id())
            || config::no_verify()
            || (config::test_free_pcs() && !config::test_coupling_graph())
        {
            consumers::ConsumerOptions::RegionInferenceContext
        } else if config::test_coupling_graph() {
            consumers::ConsumerOptions::PoloniusInputFacts
        } else {
            consumers::ConsumerOptions::PoloniusOutputFacts
        };
        let body_with_facts = consumers::get_body_with_borrowck_facts(tcx, def_id, consumer_opts);
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

#[allow(clippy::needless_lifetimes)]
#[tracing::instrument(level = "debug", skip(tcx))]
fn mir_promoted<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> (
    &'tcx Steal<mir::Body<'tcx>>,
    &'tcx Steal<IndexVec<mir::Promoted, mir::Body<'tcx>>>,
) {
    let original_mir_promoted =
        prusti_rustc_interface::interface::DEFAULT_QUERY_PROVIDERS.mir_promoted;
    let result = original_mir_promoted(tcx, def_id);
    // SAFETY: This is safe because we are feeding in the same `tcx` that is
    // going to be used as a witness when pulling out the data.
    unsafe {
        mir_storage::store_promoted_mir_body(
            tcx,
            def_id,
            result.0.borrow().clone(),
            result.1.borrow().clone(),
        );
    }
    result
}

impl prusti_rustc_interface::driver::Callbacks for PrustiCompilerCalls {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(
            |_session: &Session, providers: &mut Providers, _external: &mut ExternProviders| {
                providers.mir_borrowck = mir_borrowck;
                providers.mir_promoted = mir_promoted;
            },
        );
    }
    #[tracing::instrument(level = "debug", skip_all)]
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

    #[tracing::instrument(level = "debug", skip_all)]
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
            spec_collector.collect_specs(hir);

            let mut def_spec = spec_collector.build_def_specs();
            // Do print_typeckd_specs prior to importing cross crate
            if config::print_typeckd_specs() {
                for value in def_spec.all_values_debug(config::hide_uuids()) {
                    println!("{value}");
                }
            }
            CrossCrateSpecs::import_export_cross_crate(&mut env, &mut def_spec);
            if !config::no_verify() {
                if config::test_free_pcs() && !config::test_coupling_graph() {
                    for proc_id in env.get_annotated_procedures_and_types().0.iter() {
                        let current_procedure = env.get_procedure(*proc_id);
                        let mir = current_procedure.get_mir_rc();
                        let promoted = current_procedure.get_promoted_rc();

                        let name = env.name.get_unique_item_name(*proc_id);
                        println!("Calculating FPCS for: {name} ({:?})", mir.span);
                        test_free_pcs(&mir, &promoted, tcx);
                    }
                }
                if config::test_coupling_graph() {
                    for proc_id in env.get_annotated_procedures_and_types().0.iter() {
                        let mir = env.body.get_impure_fn_body_identity(proc_id.expect_local());
                        let facts = env
                            .body
                            .try_get_local_mir_borrowck_facts(proc_id.expect_local())
                            .unwrap();
                        let facts2 = env
                            .body
                            .try_get_local_mir_borrowck_facts2(proc_id.expect_local())
                            .unwrap();

                        let name = env.name.get_unique_item_name(*proc_id);
                        println!("Calculating CG for: {name} ({:?})", mir.span);
                        test_coupling_graph(
                            &*mir.body(),
                            &*mir.promoted(),
                            &*facts,
                            &*facts2,
                            tcx,
                            config::top_crates(),
                        );
                    }
                }
                if !config::test_free_pcs() && !config::test_coupling_graph() {
                    verify(env, def_spec);
                }
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
