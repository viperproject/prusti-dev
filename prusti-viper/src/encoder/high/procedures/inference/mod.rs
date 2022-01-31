use self::{state::FoldUnfoldState, visitor::Visitor};
use crate::encoder::{errors::SpannedEncodingResult, Encoder};
use rustc_hir::def_id::DefId;
use vir_crate::{
    high::{self as vir_high},
    middle::{self as vir_mid},
};

mod action;
mod ensurer;
mod permission;
mod semantics;
mod state;
mod visitor;

pub(super) fn infer_shape_operations<'v, 'tcx: 'v>(
    encoder: &mut Encoder<'v, 'tcx>,
    proc_def_id: DefId,
    procedure: vir_high::ProcedureDecl,
) -> SpannedEncodingResult<vir_mid::ProcedureDecl> {
    let mut visitor = Visitor::new(
        encoder,
        proc_def_id,
        FoldUnfoldState::with_parameters_and_return(
            procedure
                .parameters
                .iter()
                .map(|local| local.variable.clone()),
            procedure.returns.iter().map(|local| local.variable.clone()),
        ),
    );
    visitor.infer_procedure(procedure)
}
