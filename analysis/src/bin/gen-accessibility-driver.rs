#![feature(rustc_private)]

// Sources:
// https://github.com/rust-lang/miri/blob/master/benches/helpers/miri_helper.rs
// https://github.com/rust-lang/rust/blob/master/src/test/run-make-fulldeps/obtain-borrowck/driver.rs

use analysis::domains::DefinitelyAccessibleAnalysis;
use prusti_rustc_interface::{
    borrowck::consumers::{self, BodyWithBorrowckFacts},
    data_structures::fx::FxHashMap,
    driver::Compilation,
    errors, hir,
    hir::def_id::LocalDefId,
    interface::{interface, Config, Queries},
    middle::{
        query::{queries::mir_borrowck::ProvidedValue, ExternProviders, Providers},
        ty,
    },
    polonius_engine::{Algorithm, Output},
    session::{self, EarlyErrorHandler, Session},
    span::FileName,
};
use std::{cell::RefCell, path::PathBuf, rc::Rc};

struct OurCompilerCalls {
    args: Vec<String>,
}

mod mir_storage {
    use super::*;

    // Since mir_borrowck does not have access to any other state, we need to use a
    // thread-local for storing the obtained MIR bodies.
    //
    // Note: We are using 'static lifetime here, which is in general unsound.
    // Unfortunately, that is the only lifetime allowed here. Our use is safe
    // because we cast it back to `'tcx` before using.
    thread_local! {
        static MIR_BODIES:
            RefCell<FxHashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
            RefCell::new(FxHashMap::default());
    }

    pub unsafe fn store_mir_body<'tcx>(
        _tcx: ty::TyCtxt<'tcx>,
        def_id: LocalDefId,
        body_with_facts: BodyWithBorrowckFacts<'tcx>,
    ) {
        // SAFETY: See the module level comment.
        let body_with_facts: BodyWithBorrowckFacts<'static> = std::mem::transmute(body_with_facts);
        MIR_BODIES.with(|state| {
            let mut map = state.borrow_mut();
            assert!(map.insert(def_id, body_with_facts).is_none());
        });
    }

    #[allow(clippy::needless_lifetimes)] // We want to be very explicit about lifetimes here.
    pub unsafe fn retrieve_mir_body<'tcx>(
        _tcx: ty::TyCtxt<'tcx>,
        def_id: LocalDefId,
    ) -> BodyWithBorrowckFacts<'tcx> {
        let body_with_facts: BodyWithBorrowckFacts<'static> = MIR_BODIES.with(|state| {
            let mut map = state.borrow_mut();
            map.remove(&def_id).unwrap()
        });
        // SAFETY: See the module level comment.
        std::mem::transmute(body_with_facts)
    }
}

#[allow(clippy::needless_lifetimes)]
fn mir_borrowck<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: LocalDefId) -> ProvidedValue<'tcx> {
    let body_with_facts = consumers::get_body_with_borrowck_facts(
        tcx,
        def_id,
        consumers::ConsumerOptions::PoloniusOutputFacts,
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

impl prusti_rustc_interface::driver::Callbacks for OurCompilerCalls {
    // In this callback we override the mir_borrowck query.
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(override_queries);
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let session = compiler.session();
        session.abort_if_errors();

        assert!(self.args.iter().any(|a| a == "--generate-test-program"));

        queries.global_ctxt().unwrap().enter(|tcx| {
            // Retrieve the MIR body of all user-written functions and run Polonius.
            let mut def_ids_with_body: Vec<_> = tcx
                .mir_keys(())
                .iter()
                .flat_map(|&local_def_id| {
                    // Skip items that are not functions or methods.
                    let hir_id = tcx.hir().local_def_id_to_hir_id(local_def_id);
                    let hir_node = tcx.hir().get(hir_id);
                    match hir_node {
                        hir::Node::Item(hir::Item {
                            kind: hir::ItemKind::Fn(..),
                            ..
                        })
                        | hir::Node::ImplItem(hir::ImplItem {
                            kind: hir::ImplItemKind::Fn(..),
                            ..
                        })
                        | hir::Node::TraitItem(hir::TraitItem {
                            kind: hir::TraitItemKind::Fn(..),
                            ..
                        }) => {}
                        _ => return None,
                    }

                    // SAFETY: This is safe because we are feeding in the same `tcx`
                    // that was used to store the data.
                    let mut body_with_facts =
                        unsafe { self::mir_storage::retrieve_mir_body(tcx, local_def_id) };
                    body_with_facts.output_facts = Some(Rc::new(Output::compute(
                        body_with_facts.input_facts.as_ref().unwrap(),
                        Algorithm::Naive,
                        true,
                    )));

                    // Skip macro expansions
                    let mir_span = body_with_facts.body.span;
                    if mir_span.parent_callsite().is_some() {
                        return None;
                    }

                    // Skip short functions
                    if !session.source_map().is_multiline(mir_span) {
                        return None;
                    }

                    // Skip functions that are in an external file.
                    let source_file = session.source_map().lookup_source_file(mir_span.data().lo);
                    if let FileName::Real(filename) = &source_file.name {
                        if session.local_crate_source_file()
                            != filename.local_path().map(PathBuf::from)
                        {
                            return None;
                        }
                    } else {
                        return None;
                    }

                    Some((local_def_id, body_with_facts))
                })
                .collect();

            assert!(!def_ids_with_body.is_empty());

            // Sort according to span to ensure deterministic output
            def_ids_with_body.sort_unstable_by_key(|(_, bwf)| bwf.body.span);

            // Generate and print the programs with the additional statements to check accessibility.
            for (num, (local_def_id, body_with_facts)) in def_ids_with_body.iter().enumerate() {
                assert!(!body_with_facts
                    .input_facts
                    .as_ref()
                    .unwrap()
                    .cfg_edge
                    .is_empty());
                let body = &body_with_facts.body;

                if num > 0 {
                    println!("\n/* NEW PROGRAM */\n");
                }

                let analyzer = DefinitelyAccessibleAnalysis::new(
                    tcx,
                    local_def_id.to_def_id(),
                    body_with_facts,
                );
                match analyzer.run_analysis() {
                    Ok(state) => {
                        println!(
                            "{}",
                            state.generate_test_program(tcx, session.source_map(),)
                        );
                    }
                    Err(e) => eprintln!("{}", e.to_pretty_str(body)),
                }
            }
        });

        Compilation::Stop
    }
}

/// Run an analysis by calling like it rustc
fn main() {
    env_logger::init();
    let error_handler = EarlyErrorHandler::new(session::config::ErrorOutputType::HumanReadable(
        errors::emitter::HumanReadableErrorType::Default(errors::emitter::ColorConfig::Auto),
    ));
    prusti_rustc_interface::driver::init_rustc_env_logger(&error_handler);
    let mut compiler_args = Vec::new();
    let mut callback_args = Vec::new();
    for arg in std::env::args() {
        if arg.starts_with("--generate-test-program") {
            callback_args.push(arg);
        } else {
            compiler_args.push(arg);
        }
    }

    compiler_args.push("-Zpolonius".to_owned());
    compiler_args.push("-Zalways-encode-mir".to_owned());
    compiler_args.push("-Zcrate-attr=feature(register_tool)".to_owned());

    let mut callbacks = OurCompilerCalls {
        args: callback_args,
    };
    // Invoke compiler, and handle return code.
    let exit_code = prusti_rustc_interface::driver::catch_with_exit_code(move || {
        prusti_rustc_interface::driver::RunCompiler::new(&compiler_args, &mut callbacks).run()
    });
    std::process::exit(exit_code)
}
