// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod support_status;
#[macro_use]
mod common_validator;
mod procedure_validator;
mod pure_function_validator;
mod unsafety_validator;

use self::common_validator::CommonValidator;
use self::procedure_validator::*;
use self::pure_function_validator::*;
pub use self::support_status::Reason;
pub use self::support_status::SupportStatus;
use rustc::hir;
use rustc::hir::def_id::DefId;
use rustc::hir::intravisit::*;
use rustc::ty;
use syntax::ast::NodeId;
use syntax::codemap::Span;

pub struct Validator<'a, 'tcx: 'a> {
    tcx: ty::TyCtxt<'a, 'tcx, 'tcx>,
}

impl<'a, 'tcx: 'a> Validator<'a, 'tcx> {
    pub fn new(tcx: ty::TyCtxt<'a, 'tcx, 'tcx>) -> Self {
        Validator { tcx }
    }

    #[allow(dead_code)]
    pub fn procedure_support_status(&self, def_id: DefId) -> SupportStatus {
        let mut procedure_validator = ProcedureValidator::new(self.tcx);
        procedure_validator.check(def_id);
        procedure_validator.get_support_status()
    }

    #[allow(dead_code)]
    pub fn pure_function_support_status(&self, def_id: DefId) -> SupportStatus {
        let mut pure_function_validator = PureFunctionValidator::new(self.tcx);
        pure_function_validator.check(def_id);
        pure_function_validator.get_support_status()
    }
}
