#![feature(rustc_private)]
#![feature(associated_type_defaults)]
#![feature(box_patterns)]
#![feature(never_type)]
#![feature(allocator_api)]
#![feature(if_let_guard)]
#![allow(clippy::needless_lifetimes)]

mod encoders;
mod trait_support;
pub mod request;

use prusti_interface::{
    PrustiError,
    environment::{EnvBody, EnvDiagnostic},
};
use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use prusti_utils::config;
use task_encoder::TaskEncoder;

use crate::encoders::{
    ConstEnc, Impure, Pure,
    addr::RefDataEnc,
    custom::PairUseEnc,
    ty::{
        generics::{
            GArgsCastEnc,
            r#trait::TraitEnc,
            trait_fn::TraitFnEnc,
            trait_impls::{TraitImplEnc, TraitImplItemEnc},
        },
        interpretation::bitvec::BitVecEnc,
        lifted::{TyConstructorEnc, TypeOfEnc},
    },
};

// TODO: find a better way of handling selective verification.
// Currently, this thread local static is used to converst the initial list of defpaths from the
// `VERIFY_ONLY_DEFPATHS` option from `Vec<String>` to `Vec<DefId>`. This is done,
// so the encoder (impure/pure_function_enc) can check elements for containment.
// Because currently, it does not have the crate name available to it. But that crate name
// is part of the defpaths passed through the option.
thread_local!(
    pub static SELECTIVE_TASKS: std::cell::OnceCell<Vec<DefId>> = const { std::cell::OnceCell::new() }
);

pub fn is_selected(def_id: &DefId) -> bool {
    SELECTIVE_TASKS.with(|selective_tasks| {
        selective_tasks
            .get()
            .as_ref()
            .is_none_or(|procs| procs.contains(def_id))
    })
}

pub fn test_entrypoint<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    body: EnvBody<'tcx>,
    def_spec: prusti_interface::specs::typed::DefSpecificationMap,
    // this is None if the verification is not selective - all procedures should be encoded.
    // if the verification is selective, only the procedures in this vector should be encoded with body
    procedures: Option<Vec<DefId>>,
    env_diagnostic: &EnvDiagnostic<'tcx>,
) -> request::RequestWithContext {
    let ident_style = if config::short_viper_names() {
        vir::IdentStyle::ItemName
    } else {
        vir::IdentStyle::DefPath
    };
    vir::init_vcx(vir::VirCtxt::new(tcx, body, def_spec, ident_style));
    SELECTIVE_TASKS.with(|selective_tasks| {
        if let Some(procs) = procedures {
            selective_tasks
                .set(procs)
                .expect("Selective tasks were already set");
        }
    });

    crate::encoders::encode_all_in_crate(tcx);
    task_encoder::drain_triggers();

    if config::show_ide_info() {
        vir::with_vcx(|vcx| vcx.emit_contract_spans(env_diagnostic));
    }
    let mut program = task_encoder::Program::default();

    // We output results from both monomorphic and polymorphic encoding of
    // functions, because even when Prusti is configured to use the monomorphic
    // it will still use `MirPolyImpureEnc` directly sometimes (see usages
    // earlier in this file).
    program.header("user functions");
    crate::encoders::FunctionCallEnc::emit_outputs(&mut program);

    program.header("user methods");
    crate::encoders::MethodCallEnc::emit_outputs(&mut program);

    program.header("MIR builtins");
    crate::encoders::MirBuiltinUnOpEnc::emit_outputs(&mut program);
    crate::encoders::MirBuiltinBinOpEnc::emit_outputs(&mut program);
    crate::encoders::MirBuiltinUseCastEnc::emit_outputs(&mut program);
    // Unsize casts call `metadata_cast`; the `&mut` methods call
    // `value_cast`. Both domains must be emitted too.
    crate::encoders::MetadataCastEnc::emit_outputs(&mut program);
    crate::encoders::ValueCastEnc::emit_outputs(&mut program);
    crate::encoders::MetadataCastAxiomEnc::emit_outputs(&mut program);
    crate::encoders::ValueCastAxiomEnc::emit_outputs(&mut program);
    crate::encoders::PrustiBuiltinEnc::emit_outputs(&mut program);

    program.header("pure generic casts");
    GArgsCastEnc::<Pure>::emit_outputs(&mut program);

    program.header("impure generic casts");
    GArgsCastEnc::<Impure>::emit_outputs(&mut program);

    program.header("snapshots");
    crate::encoders::TyUsePureEnc::emit_outputs(&mut program);
    BitVecEnc::emit_outputs(&mut program);

    program.header("predicates");
    crate::encoders::TyUseImpureEnc::emit_outputs(&mut program);

    program.header("type constructors");
    TyConstructorEnc::emit_outputs(&mut program);
    TypeOfEnc::emit_outputs(&mut program);
    crate::encoders::TyInhabitedEnc::emit_outputs(&mut program);

    program.header("constants");
    ConstEnc::emit_outputs(&mut program);

    program.header("custom");
    PairUseEnc::emit_outputs(&mut program);
    RefDataEnc::emit_outputs(&mut program);

    program.header("traits");
    TraitEnc::emit_outputs(&mut program);
    TraitFnEnc::emit_outputs(&mut program);
    TraitImplEnc::emit_outputs(&mut program);
    TraitImplItemEnc::emit_outputs(&mut program);

    if std::env::var("LOCAL_TESTING").is_ok() {
        std::fs::write("local-testing/simple.vpr", program.code()).unwrap();
    }

    for (error_msg, span) in program.encoder_errors().drain(..) {
        PrustiError::internal(error_msg, span.into()).emit(env_diagnostic);
    }

    // Errors raised during encoding (e.g. an unsupported feature that was
    // replaced by an abstract stub) so that they surface rather than silently
    // degrading.
    for error in early_errors() {
        error.emit(env_diagnostic);
    }

    let program = program.mk_program();

    request::RequestWithContext {
        program: program.to_ref(),
    }
}

pub fn early_errors() -> Vec<PrustiError> {
    vir::with_vcx(|vcx| vcx.early_errors())
}

pub fn backtranslate_error(
    error_kind: &str,
    offending_pos_id: usize,
    reason_pos_id: Option<usize>,
) -> Vec<PrustiError> {
    vir::with_vcx(|vcx| vcx.backtranslate(error_kind, offending_pos_id, reason_pos_id))
}
