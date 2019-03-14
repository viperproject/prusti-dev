#[macro_use]
mod support_status;
mod procedure_validator;
mod pure_function_validator;
mod unsafety_validator;

pub use self::support_status::SupportStatus;
pub use self::support_status::SupportKind;
use self::procedure_validator::*;
use self::pure_function_validator::*;
use syntax::ast::NodeId;
use rustc::hir;
use rustc::hir::intravisit::*;
use syntax::codemap::Span;
use rustc::ty;
use rustc::hir::def_id::DefId;

pub struct Validator<'a, 'tcx: 'a> {
    tcx: ty::TyCtxt<'a, 'tcx, 'tcx>
}

impl<'a, 'tcx: 'a> Validator<'a, 'tcx> {
    pub fn new(tcx: ty::TyCtxt<'a, 'tcx, 'tcx>) -> Self {
        Validator {
            tcx
        }
    }

    #[allow(dead_code)]
    pub fn procedure_support_status(&self, fk: FnKind<'tcx>, fd: &hir::FnDecl, b: hir::BodyId, s: Span, id: NodeId) -> SupportStatus {
        let mut procedure_validator = ProcedureValidator::new(self.tcx);
        procedure_validator.check_fn(fk, fd, b, s, id);
        procedure_validator.get_support_status()
    }

    #[allow(dead_code)]
    pub fn pure_function_support_status(&self, fk: FnKind<'tcx>, fd: &hir::FnDecl, b: hir::BodyId, s: Span, id: NodeId) -> SupportStatus {
        let mut pure_function_validator = PureFunctionValidator::new(self.tcx);
        pure_function_validator.check_fn(fk, fd, b, s, id);
        pure_function_validator.get_support_status()
    }

    #[allow(dead_code)]
    pub fn procedure_item_support_status(&self, def_id: DefId) -> SupportStatus {
        let mut procedure_validator = ProcedureValidator::new(self.tcx);
        procedure_validator.check_fn_item(def_id);
        procedure_validator.get_support_status()
    }

    #[allow(dead_code)]
    pub fn pure_function_item_support_status(&self, def_id: DefId) -> SupportStatus {
        let mut pure_function_validator = PureFunctionValidator::new(self.tcx);
        pure_function_validator.check_fn_item(def_id);
        pure_function_validator.get_support_status()
    }
}
