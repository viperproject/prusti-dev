use crate::{modify_mir, verifier::verify};

use prusti_common::config;
use prusti_interface::{
    environment::{mir_storage, Environment},
    specs::{self, cross_crate::CrossCrateSpecs, is_spec_fn, typed::DefSpecificationMap},
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

impl prusti_rustc_interface::driver::Callbacks for PrustiCompilerCalls {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(
            |_session: &Session, providers: &mut Providers, _external: &mut ExternProviders| {
                providers.mir_borrowck = mir_borrowck;
                providers.mir_promoted = mir_promoted;
                providers.mir_drops_elaborated_and_const_checked =
                    modify_mir::mir_modify::mir_drops_elaborated;
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
        // can we modify ast? just stealing it does not work obviously..
        //  queries.global_ctxt().unwrap().enter(|tcx: TyCtxt<'tcx>| {
        //     let (resolver, mut krate_rc) = tcx.resolver_for_lowering(()).steal();
        //     let krate: &mut Crate = Rc::get_mut(&mut krate_rc).unwrap();
        //     // let _visitor = MutVisitor;
        //     tcx.arena.alloc(Steal::new((resolver, Rc::new(krate.clone()))))
        // });

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
            let (def_spec, env) = get_specs(tcx, Some(compiler));
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

pub fn get_specs<'tcx>(
    tcx: TyCtxt<'tcx>,
    compiler_opt: Option<&Compiler>,
) -> (DefSpecificationMap, Environment<'tcx>) {
    let specs_env_opt = unsafe { crate::SPEC_ENV.take() };
    if let Some((specs, env)) = specs_env_opt {
        let env_tcx: Environment<'tcx> = unsafe { std::mem::transmute(env) };
        (specs, env_tcx)
    } else {
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
}
