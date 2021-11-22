#![feature(rustc_private)]

extern crate polonius_engine;
/// Sources:
/// https://github.com/rust-lang/miri/blob/master/benches/helpers/miri_helper.rs
/// https://github.com/rust-lang/rust/blob/master/src/test/run-make-fulldeps/obtain-borrowck/driver.rs
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;

use analysis::{
    abstract_interpretation::FixpointEngine,
    domains::{DefinitelyInitializedAnalysis, MaybeBorrowedAnalysis, ReachingDefsAnalysis},
};
use polonius_engine::{Algorithm, Output};
use rustc_ast::ast;
use rustc_borrowck::BodyWithBorrowckFacts;
use rustc_driver::Compilation;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_interface::{interface, Config, Queries};
use rustc_middle::{
    ty,
    ty::query::{query_values::mir_borrowck, ExternProviders, Providers},
};
use rustc_session::{Attribute, Session};
use std::{cell::RefCell, collections::HashMap, rc::Rc};

struct OurCompilerCalls {
    args: Vec<String>,
}

fn get_attribute<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: DefId,
    segment1: &str,
    segment2: &str,
) -> Option<&'tcx Attribute> {
    tcx.get_attrs(def_id).iter().find(|attr| match &attr.kind {
        ast::AttrKind::Normal(
            ast::AttrItem {
                path:
                    ast::Path {
                        span: _,
                        segments,
                        tokens: _,
                    },
                args: ast::MacArgs::Empty,
                tokens: _,
            },
            _,
        ) => {
            segments.len() == 2
                && segments[0].ident.as_str() == segment1
                && segments[1].ident.as_str() == segment2
        }
        _ => false,
    })
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
            RefCell<HashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
            RefCell::new(HashMap::new());
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
fn mir_borrowck<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: LocalDefId) -> mir_borrowck<'tcx> {
    let body_with_facts = rustc_borrowck::consumers::get_body_with_borrowck_facts(
        tcx,
        ty::WithOptConstParam::unknown(def_id),
    );
    // SAFETY: This is safe because we are feeding in the same `tcx` that is
    // going to be used as a witness when pulling out the data.
    unsafe {
        mir_storage::store_mir_body(tcx, def_id, body_with_facts);
    }
    let mut providers = Providers::default();
    rustc_borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

fn override_queries(_session: &Session, local: &mut Providers, _external: &mut ExternProviders) {
    local.mir_borrowck = mir_borrowck;
}

impl rustc_driver::Callbacks for OurCompilerCalls {
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
        compiler.session().abort_if_errors();

        let abstract_domain: &str = self
            .args
            .iter()
            .filter(|a| a.starts_with("--analysis"))
            .flat_map(|a| a.rsplit('='))
            .next()
            .expect("Please add --analysis=<DOMAIN>");

        println!(
            "Analyzing file {} using {}...",
            compiler.input().source_name().prefer_local(),
            abstract_domain
        );

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            // collect all functions with attribute #[analyzer::run]
            let mut local_def_ids: Vec<_> = tcx
                .mir_keys(())
                .iter()
                .filter(|id| get_attribute(tcx, id.to_def_id(), "analyzer", "run").is_some())
                .collect();

            // sort according to argument span to ensure deterministic output
            local_def_ids.sort_unstable_by_key(|id| {
                get_attribute(tcx, id.to_def_id(), "analyzer", "run")
                    .unwrap()
                    .span
            });

            for &local_def_id in local_def_ids {
                println!(
                    "Result for function {}():",
                    tcx.item_name(local_def_id.to_def_id())
                );

                // SAFETY: This is safe because we are feeding in the same `tcx`
                // that was used to store the data.
                let mut body_with_facts =
                    unsafe { self::mir_storage::retrieve_mir_body(tcx, local_def_id) };
                body_with_facts.output_facts = Rc::new(Output::compute(
                    &body_with_facts.input_facts,
                    Algorithm::Naive,
                    true,
                ));
                assert!(!body_with_facts.input_facts.cfg_edge.is_empty());
                let body = &body_with_facts.body;

                match abstract_domain {
                    "ReachingDefsAnalysis" => {
                        let result = ReachingDefsAnalysis::new(tcx, local_def_id.to_def_id(), body)
                            .run_fwd_analysis();
                        match result {
                            Ok(state) => {
                                println!("{}", serde_json::to_string_pretty(&state).unwrap())
                            }
                            Err(e) => eprintln!("{}", e.to_pretty_str(body)),
                        }
                    }
                    "DefinitelyInitializedAnalysis" => {
                        let result =
                            DefinitelyInitializedAnalysis::new(tcx, local_def_id.to_def_id(), body)
                                .run_fwd_analysis();
                        match result {
                            Ok(state) => {
                                println!("{}", serde_json::to_string_pretty(&state).unwrap())
                            }
                            Err(e) => eprintln!("{}", e.to_pretty_str(body)),
                        }
                    }
                    "RelaxedDefinitelyInitializedAnalysis" => {
                        let result = DefinitelyInitializedAnalysis::new_relaxed(
                            tcx,
                            local_def_id.to_def_id(),
                            body,
                        )
                        .run_fwd_analysis();
                        match result {
                            Ok(state) => {
                                println!("{}", serde_json::to_string_pretty(&state).unwrap())
                            }
                            Err(e) => eprintln!("{}", e.to_pretty_str(body)),
                        }
                    }
                    "MaybeBorrowedAnalysis" => {
                        let analyzer = MaybeBorrowedAnalysis::new(&body_with_facts);
                        match analyzer.run_analysis() {
                            Ok(state) => {
                                println!("{}", serde_json::to_string_pretty(&state).unwrap())
                            }
                            Err(e) => eprintln!("{}", e.to_pretty_str(body)),
                        }
                    }
                    _ => panic!("Unknown domain argument: {}", abstract_domain),
                }
            }
        });

        compiler.session().abort_if_errors();

        Compilation::Stop
    }
}

/// Run an analysis by calling like it rustc
///
/// Give arguments to the analyzer by prefixing them with '--analysis'
/// A abstract domain has to be provided by using '--analysis=' (without spaces), e.g.:
/// --analysis=ReachingDefsState or --analysis=DefinitelyInitializedAnalysis
fn main() {
    env_logger::init();
    rustc_driver::init_rustc_env_logger();
    let mut compiler_args = Vec::new();
    let mut callback_args = Vec::new();
    for arg in std::env::args() {
        if arg.starts_with("--analysis") {
            callback_args.push(arg);
        } else {
            compiler_args.push(arg);
        }
    }

    compiler_args.push("-Zpolonius".to_owned());
    compiler_args.push("-Zalways-encode-mir".to_owned());
    compiler_args.push("-Zcrate-attr=feature(register_tool)".to_owned());
    compiler_args.push("-Zcrate-attr=register_tool(analyzer)".to_owned());

    let mut callbacks = OurCompilerCalls {
        args: callback_args,
    };
    // Invoke compiler, and handle return code.
    let exit_code = rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&compiler_args, &mut callbacks).run()
    });
    std::process::exit(exit_code)
}
