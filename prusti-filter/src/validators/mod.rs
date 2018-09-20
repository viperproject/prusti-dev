#[macro_use]
mod support_status;
mod procedure_validator;
mod pure_function_validator;

pub use self::support_status::SupportStatus;
use self::procedure_validator::*;
use self::pure_function_validator::*;
use syntax::ast::NodeId;
use rustc::hir;
use rustc::hir::intravisit::*;
use syntax::codemap::Span;
use rustc::ty;
use rustc::hir::def_id::DefId;

pub struct Validator<'a, 'tcx: 'a> {
    procedure_validator: ProcedureValidator<'a, 'tcx>,
    pure_function_validator: PureFunctionValidator<'a, 'tcx>,
}

impl<'a, 'tcx: 'a> Validator<'a, 'tcx> {
    pub fn new(tcx: ty::TyCtxt<'a, 'tcx, 'tcx>) -> Self {
        Validator {
            procedure_validator: ProcedureValidator::new(tcx),
            pure_function_validator: PureFunctionValidator::new(tcx),
        }
    }

    pub fn is_supported_procedure(&self, fk: FnKind<'tcx>, fd: &hir::FnDecl, b: hir::BodyId, s: Span, id: NodeId) -> SupportStatus {
        self.procedure_validator.is_supported_fn(fk, fd, b, s, id)
    }

    pub fn is_supported_pure_function(&self, fk: FnKind<'tcx>, fd: &hir::FnDecl, b: hir::BodyId, s: Span, id: NodeId) -> SupportStatus {
        self.pure_function_validator.is_supported_fn(fk, fd, b, s, id)
    }

    pub fn is_supported_procedure_item(&self, def_id: DefId) -> SupportStatus {
        self.procedure_validator.is_supported_fn_item(def_id)
    }

    pub fn is_supported_pure_function_item(&self, def_id: DefId) -> SupportStatus {
        self.pure_function_validator.is_supported_fn_item(def_id)
    }
}
