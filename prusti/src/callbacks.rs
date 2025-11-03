use crate::verifier::verify;
use ::log::{debug, info};
use ide::{fake_error, IdeInfo};
use prusti_interface::{
    data::VerificationTask,
    environment::{mir_storage, Environment},
    specs::{self, cross_crate::CrossCrateSpecs, is_spec_fn},
    PrustiError,
};
use prusti_rustc_interface::{
    borrowck::consumers,
    data_structures::steal::Steal,
    driver::Compilation,
    hir::{def::DefKind, def_id::LocalDefId},
    index::IndexVec,
    interface::{interface::Compiler, Config},
    middle::{
        mir, query::queries::mir_borrowck::ProvidedValue as MirBorrowck, ty::TyCtxt,
        util::Providers,
    },
    session::Session,
    span::DUMMY_SP,
};
use prusti_utils::config;

#[derive(Default)]
pub struct PrustiCompilerCalls;

// Running `get_body_with_borrowck_facts` can be very slow, therefore we avoid it when not
// necessary; for crates which won't be verified or spec_fns it suffices to load just the fn body

#[allow(clippy::needless_lifetimes)]
#[tracing::instrument(level = "debug", skip(tcx))]
fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> MirBorrowck<'tcx> {
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
        let body_with_facts = consumers::get_bodies_with_borrowck_facts(tcx, def_id, consumer_opts);
        for (def_id, body) in body_with_facts {
            // SAFETY: This is safe because we are feeding in the same `tcx` that is
            // going to be used as a witness when pulling out the data.
            unsafe {
                mir_storage::store_mir_body(tcx, def_id, body);
            }
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

struct NoAnn;

impl prusti_rustc_interface::ast_pretty::pprust::PpAnn for NoAnn {}

impl prusti_rustc_interface::driver::Callbacks for PrustiCompilerCalls {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(|_session: &Session, providers: &mut Providers| {
            providers.mir_borrowck = mir_borrowck;
            providers.mir_promoted = mir_promoted;
        });
    }

    #[tracing::instrument(level = "debug", skip_all)]
    fn after_expansion<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        if compiler.sess.is_rust_2015() {
            compiler
                .sess
                .dcx()
                .struct_warn(
                    "Prusti specifications are supported only from 2018 edition. Please \
                    specify the edition with adding a command line argument `--edition=2018` or \
                    `--edition=2021`.",
                )
                .emit();
        }
        compiler.sess.dcx().abort_if_errors();
        if config::print_desugared_specs() {
            // based on the implementation of rustc_driver::pretty::print_after_parsing
            let sess = &compiler.sess;
            let krate = &tcx.resolver_for_lowering().borrow().1;
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
                    &NoAnn,
                    false,
                    sess.edition(),
                    &sess.psess.attr_id_generator,
                )
            );
        }
        Compilation::Continue
    }

    #[tracing::instrument(level = "debug", skip_all)]
    fn after_analysis<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        compiler.sess.dcx().abort_if_errors();
        let mut env = Environment::new(tcx, env!("CARGO_PKG_VERSION"));
        let spec_checker = specs::checker::SpecChecker::new();
        spec_checker.check(&env);
        compiler.sess.dcx().abort_if_errors();

        let mut spec_collector = specs::SpecCollector::new(&mut env);
        spec_collector.collect_specs();

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
            let compiler_info = IdeInfo::collect(&env, &annotated_procedures, &def_spec);
            let out = serde_json::to_string(&compiler_info).unwrap();
            PrustiError::message(format!("compilerInfo{out}"), DUMMY_SP.into())
                .emit(&env.diagnostic);
        }
        // as long as we have to throw a fake error we need to check this
        // note that is_single_file will still be false if this is run through x.py.
        // it will find a manifest in prusti-launch but CARGO_PRIMARY_PACKAGE will still
        // not be ok. meaning that selective verification can't currently be tested through
        // x.py if the target is a single-file program.
        let is_single_file = std::env::var("CARGO_MANIFEST_DIR").is_err();
        let is_primary_package = is_single_file || std::env::var("CARGO_PRIMARY_PACKAGE").is_ok();

        // collect and output Information used by IDE:
        if !config::no_verify() && !config::skip_verification() {
            let target_def_paths = config::verify_only_defpaths();
            debug!(
                "Received def paths: {target_def_paths:?}. Package is primary: {is_primary_package}, Package is single-file: {is_single_file}"
            );
            if !target_def_paths.is_empty() {
                // if we do selective verification, then definitely only
                // for methods of the primary package. Check needed because
                // of the fake_error, otherwise verification stops early
                // with local dependencies
                if is_primary_package {
                    let procedures = annotated_procedures
                        .into_iter()
                        .filter(|x| target_def_paths.contains(&env.name.get_unique_item_name(*x)))
                        .collect::<Vec<_>>();
                    if !procedures.is_empty() {
                        let selective_task = VerificationTask {
                            procedures,
                            types,
                            selective: true,
                        };
                        verify(env, def_spec, selective_task);
                    } else {
                        info!("Passed selective defpaths were empty or had no matching procedures - skipping verification.");
                    }
                    // fake_error(&env_diagnostic);
                }
            } else {
                let verification_task = VerificationTask {
                    procedures: annotated_procedures,
                    types,
                    selective: false,
                };
                verify(env, def_spec, verification_task);
            }
        } else if config::skip_verification() && !config::no_verify() && is_primary_package {
            // add a fake error, reason explained in issue #1261
            fake_error(&env.diagnostic);
        }

        compiler.sess.dcx().abort_if_errors();
        if config::full_compilation() {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}
