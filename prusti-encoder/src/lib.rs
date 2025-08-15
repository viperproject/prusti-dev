#![feature(rustc_private)]
#![feature(associated_type_defaults)]
#![feature(box_patterns)]
#![feature(never_type)]
#![feature(allocator_api)]
#![allow(clippy::needless_lifetimes)]

mod encoders;
mod encoder_traits;
mod trait_support;
pub mod request;

use prusti_interface::{environment::EnvBody, specs::specifications::SpecQuery, PrustiError};
use prusti_rustc_interface::{hir, middle::ty};
use task_encoder::TaskEncoder;

use crate::encoders::{
    lifted::{
        CastTypeImpure, CastTypePure, CastersEnc, LiftedConstEnc, TyConstructorEnc, TypeOfEnc
    },
    MirPolyImpureEnc,
};

pub fn test_entrypoint<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    body: EnvBody<'tcx>,
    def_spec: prusti_interface::specs::typed::DefSpecificationMap,
) -> request::RequestWithContext {
    vir::init_vcx(vir::VirCtxt::new(tcx, body, def_spec));

    // TODO: this should be a "crate" encoder, which will deps.require all the methods in the crate

    for def_id in tcx.hir_body_owners() {
        tracing::debug!("test_entrypoint item: {def_id:?}");
        let kind = tcx.def_kind(def_id);
        match kind {
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                let def_id = def_id.to_def_id();
                if prusti_interface::specs::is_spec_fn(tcx, def_id) {
                    continue;
                }

                let (is_pure, is_trusted) = crate::encoders::with_proc_spec(
                    SpecQuery::GetProcKind(def_id, ty::List::identity_for_item(tcx, def_id)),
                    |proc_spec| {
                        let is_pure = proc_spec.kind.is_pure().unwrap_or_default();
                        let is_trusted = proc_spec.trusted.extract_inherit().unwrap_or_default();
                        (is_pure, is_trusted)
                    },
                )
                .unwrap_or_default();

                if !(is_trusted && is_pure) {
                    let res = MirPolyImpureEnc::encode(def_id, false);
                    assert!(res.is_ok());
                }
            }
            unsupported_item_kind => {
                tracing::debug!("unsupported item: {unsupported_item_kind:?}");
            }
        }
    }
    
    let mut program = task_encoder::Program::default();

    // We output results from both monomorphic and polymorphic encoding of
    // functions, because even when Prusti is configured to use the monomorphic
    // it will still use `MirPolyImpureEnc` directly sometimes (see usages
    // earlier in this file).
    program.header("user methods");
    crate::encoders::MirPolyImpureEnc::emit_outputs(&mut program);

    program.header("user functions");
    crate::encoders::PureFunctionEnc::emit_outputs(&mut program);

    program.header("MIR builtins");
    crate::encoders::MirBuiltinEnc::emit_outputs(&mut program);

    program.header("pure generic casts");
    CastersEnc::<CastTypePure>::emit_outputs(&mut program);

    program.header("impure generic casts");
    CastersEnc::<CastTypeImpure>::emit_outputs(&mut program);
    
    program.header("snapshots");
    crate::encoders::TyPureEnc::emit_outputs(&mut program);

    program.header("predicates");
    crate::encoders::TyImpureEnc::emit_outputs(&mut program);

    program.header("type constructors");
    TyConstructorEnc::emit_outputs(&mut program);
    TypeOfEnc::emit_outputs(&mut program);

    program.header("const generics");
    LiftedConstEnc::emit_outputs(&mut program);

    if std::env::var("LOCAL_TESTING").is_ok() {
        std::fs::write("local-testing/simple.vpr", program.code()).unwrap();
    }

    let program = program.mk_program();

    /*
    let source_path = std::path::Path::new("source/path"); // TODO: env.name.source_path();
    let rust_program_name = source_path
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .to_owned();
    */

    request::RequestWithContext {
        program: program.to_ref(),
    }
}

pub fn backtranslate_error(
    error_kind: &str,
    offending_pos_id: usize,
    reason_pos_id: Option<usize>,
) -> Option<Vec<PrustiError>> {
    vir::with_vcx(|vcx| vcx.backtranslate(error_kind, offending_pos_id, reason_pos_id))
}
