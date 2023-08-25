use crate::{modify_mir::mir_modify, verifier::verify};

use prusti_common::config;
use prusti_interface::{
    environment::{mir_storage, Environment},
    globals,
    specs::{self, cross_crate::CrossCrateSpecs, is_spec_fn, typed::DefSpecificationMap},
};
use prusti_rustc_interface::{
    borrowck::consumers,
    data_structures::steal::Steal,
    driver::Compilation,
    hir::def::DefKind,
    index::IndexVec,
    interface::{interface::Compiler, Config, Queries, DEFAULT_QUERY_PROVIDERS},
    middle::{
        mir::{self, BorrowCheckResult, MirPass, START_BLOCK},
        query::{ExternProviders, Providers},
        ty::{self, TyCtxt, TypeVisitableExt},
    },
    mir_transform::{self, inline},
    span::def_id::{LocalDefId, LOCAL_CRATE},
    trait_selection::traits,
    session::{EarlyErrorHandler, Session},
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
        let consumer_opts = if is_spec_fn(tcx, def_id.to_def_id()) || config::no_verify() {
            consumers::ConsumerOptions::RegionInferenceContext
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
        mir_storage::store_promoted_mir_body(tcx, def_id, result.0.borrow().clone());
    }
    result
}

// a copy of the rust compilers implementation of this query +
// + verification on its first call
// + dead code elimination if enabled
// + insertion of runtime checks if enabled
pub(crate) fn mir_drops_elaborated(tcx: TyCtxt<'_>, def: LocalDefId) -> &Steal<mir::Body<'_>> {
    // run verification here, otherwise we can't rely on results in
    // drops elaborated
    if config::no_verify() {
        return (DEFAULT_QUERY_PROVIDERS.mir_drops_elaborated_and_const_checked)(tcx, def);
    }
    let def_id = def.to_def_id();
    if !globals::verified(def_id.krate) {
        let (def_spec, env) = get_specs(tcx, None);
        println!("Starting Verification");
        let env = verify(env, def_spec.clone());
        globals::set_verified(def_id.krate);
        globals::store_spec_env(def_spec, env);
    }

    // original compiler code
    if tcx.sess.opts.unstable_opts.drop_tracking_mir
        && let DefKind::Generator = tcx.def_kind(def)
    {
        tcx.ensure_with_value().mir_generator_witnesses(def);
    }
    let mir_borrowck = tcx.mir_borrowck(def);

    let is_fn_like = tcx.def_kind(def).is_fn_like();
    if is_fn_like {
        // Do not compute the mir call graph without said call graph actually being used.
        if inline::Inline.is_enabled(&tcx.sess) {
            tcx.ensure_with_value()
                .mir_inliner_callees(ty::InstanceDef::Item(def.to_def_id()));
        }
    }

    let (body, _) = tcx.mir_promoted(def);
    let mut body = body.steal();

    // ################################################
    // Inserted Modifications
    // ################################################
    let local_decls = body.local_decls.clone();
    if config::remove_dead_code() {
        mir_modify::dead_code_elimination(tcx, &mut body, def_id);
    }
    if config::insert_runtime_checks() {
        mir_modify::insert_runtime_checks(&mut body, def_id, tcx, &local_decls);
    }
    // ################################################
    // End of Modifications, back to original compiler
    // code!
    // ################################################

    if let Some(error_reported) = mir_borrowck.tainted_by_errors {
        body.tainted_by_errors = Some(error_reported);
    }
    let predicates = tcx
        .predicates_of(body.source.def_id())
        .predicates
        .iter()
        .filter_map(|(p, _)| if p.is_global() { Some(*p) } else { None });
    if traits::impossible_predicates(tcx, traits::elaborate(tcx, predicates).collect()) {
        // Clear the body to only contain a single `unreachable` statement.
        let bbs = body.basic_blocks.as_mut();
        bbs.raw.truncate(1);
        bbs[START_BLOCK].statements.clear();
        bbs[START_BLOCK].terminator_mut().kind = mir::TerminatorKind::Unreachable;
        body.var_debug_info.clear();
        body.local_decls.raw.truncate(body.arg_count + 1);
    }

    mir_transform::run_analysis_to_runtime_passes(tcx, &mut body);

    // Only available once rust is updated!
    // Now that drop elaboration has been performed, we can check for
    // unconditional drop recursion.
    // mir_build::lints::check_drop_recursion(tcx, &body);

    tcx.alloc_steal_mir(body)
}

impl prusti_rustc_interface::driver::Callbacks for PrustiCompilerCalls {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(
            |_session: &Session, providers: &mut Providers, _external: &mut ExternProviders| {
                providers.mir_borrowck = mir_borrowck;
                providers.mir_promoted = mir_promoted;
                providers.mir_drops_elaborated_and_const_checked = mir_drops_elaborated;
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
        _error_handler: &EarlyErrorHandler,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();
        queries.global_ctxt().unwrap().enter(|tcx| {
            if !globals::verified(LOCAL_CRATE) {
                let (def_spec, env) = get_specs(tcx, Some(compiler));
                if !config::no_verify() {
                    let env = verify(env, def_spec.clone());

                    globals::set_verified(LOCAL_CRATE);
                    globals::store_spec_env(def_spec, env);
                }
            }
        });
        compiler.session().abort_if_errors();
        if config::full_compilation() {
            // verification moved into mir_drops_elaborated query!
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

pub fn get_specs<'tcx>(
    tcx: TyCtxt<'tcx>,
    compiler_opt: Option<&Compiler>,
) -> (DefSpecificationMap, Environment<'tcx>) {
    let mut env = Environment::new(tcx, env!("CARGO_PKG_VERSION"));

    // when get_specs is first called from an overriden query
    // (as is the case for runtime checks), we don't have
    // access to the compiler, so for now we just skip the
    // checking then
    if let Some(compiler) = compiler_opt {
        let spec_checker = specs::checker::SpecChecker::new();
        spec_checker.check(&env);
        compiler.session().abort_if_errors();
    } else if env.diagnostic.has_errors() {
        // TODO: still give some sensible error?
        // Does it make a difference if we show the errors
        // once get_specs returns in callbacks?
        panic!("Spec checking caused errors. No good error message because runtime checks are enabled. This is a TODO");
    }
    let hir = env.query.hir();
    let mut spec_collector = specs::SpecCollector::new(&mut env);
    spec_collector.collect_specs(hir);

    let mut def_spec = spec_collector.build_def_specs();
    if config::print_typeckd_specs() {
        for value in def_spec.all_values_debug(config::hide_uuids()) {
            println!("{value}");
        }
    }
    CrossCrateSpecs::import_export_cross_crate(&mut env, &mut def_spec);
    (def_spec, env)
}
