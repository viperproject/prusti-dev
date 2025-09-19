#![feature(rustc_private)]
#![feature(associated_type_defaults)]
#![feature(box_patterns)]
#![feature(never_type)]
#![feature(allocator_api)]
#![allow(clippy::needless_lifetimes)]

mod encoders;
mod trait_support;
pub mod request;

use prusti_interface::{PrustiError, environment::EnvBody};
use prusti_rustc_interface::middle::ty;
use task_encoder::TaskEncoder;

use crate::encoders::{
    Impure, Pure,
    ty::{
        generics::GArgsCastEnc,
        lifted::{TyConstructorEnc, TypeOfEnc},
    },
};

pub fn test_entrypoint<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    body: EnvBody<'tcx>,
    def_spec: prusti_interface::specs::typed::DefSpecificationMap,
) -> request::RequestWithContext {
    vir::init_vcx(vir::VirCtxt::new(tcx, body, def_spec));
    unsafe { backtrace_on_stack_overflow::enable() };

    // TODO: this should be a "crate" encoder, which will deps.require all the methods in the crate

    crate::encoders::encode_all_in_crate(tcx);

    let mut program = task_encoder::Program::default();

    // We output results from both monomorphic and polymorphic encoding of
    // functions, because even when Prusti is configured to use the monomorphic
    // it will still use `MirPolyImpureEnc` directly sometimes (see usages
    // earlier in this file).
    program.header("user methods");
    crate::encoders::FunctionCallEnc::emit_outputs(&mut program);

    program.header("user functions");
    crate::encoders::MethodCallEnc::emit_outputs(&mut program);

    program.header("MIR builtins");
    crate::encoders::MirBuiltinEnc::emit_outputs(&mut program);

    program.header("pure generic casts");
    GArgsCastEnc::<Pure>::emit_outputs(&mut program);

    program.header("impure generic casts");
    GArgsCastEnc::<Impure>::emit_outputs(&mut program);

    program.header("snapshots");
    crate::encoders::TyUsePureEnc::emit_outputs(&mut program);

    program.header("predicates");
    crate::encoders::TyUseImpureEnc::emit_outputs(&mut program);

    program.header("type constructors");
    TyConstructorEnc::emit_outputs(&mut program);
    TypeOfEnc::emit_outputs(&mut program);

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

pub fn early_errors() -> Vec<PrustiError> {
    vir::with_vcx(|vcx| vcx.early_errors())
}

pub fn backtranslate_error(
    error_kind: &str,
    offending_pos_id: usize,
    reason_pos_id: Option<usize>,
) -> Option<Vec<PrustiError>> {
    vir::with_vcx(|vcx| vcx.backtranslate(error_kind, offending_pos_id, reason_pos_id))
}
