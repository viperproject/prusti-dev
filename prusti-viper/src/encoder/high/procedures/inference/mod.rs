//! This module contains the code for inferring ghost operations such as `fold`
//! and `unfold`. Since in the presence of unsafe code we cannot be sure that
//! this algorithm will always succeed, we track under which conditions a
//! specific folding state exists. The key observation is that each
//! stack-allocated variable is allocated and deallocated only as a whole.
//! Threrefore, for each variable we track its unfolding state, which can be
//! either unconditional (the state is the same on all incoming paths) or
//! conditional (the state depends on the incoming path).
//!
//! The data structures used for tracking the state are in the `state` module.

use self::{state::FoldUnfoldState, visitor::Visitor};
use crate::encoder::{errors::SpannedEncodingResult, Encoder};
use prusti_common::config;
use prusti_rustc_interface::hir::def_id::DefId;
use vir_crate::{
    common::graphviz::ToGraphviz,
    middle::{self as vir_mid},
    typed::{self as vir_typed},
};

mod action;
mod ensurer;
mod permission;
mod semantics;
mod state;
mod visitor;
mod unfolding_expressions;
mod eval_using;

#[tracing::instrument(level = "debug", skip(encoder, procedure), fields(procedure = %procedure))]
pub(super) fn infer_shape_operations<'v, 'tcx: 'v>(
    encoder: &mut Encoder<'v, 'tcx>,
    proc_def_id: DefId,
    procedure: vir_typed::ProcedureDecl,
) -> SpannedEncodingResult<vir_mid::ProcedureDecl> {
    if config::dump_debug_info() {
        let source_filename = encoder.env().name.source_file_name();
        prusti_common::report::log::report_with_writer(
            "graphviz_method_before_foldunfold",
            format!("{}.{}.dot", source_filename, procedure.name),
            |writer| procedure.to_graphviz(writer).unwrap(),
        );
    }
    let mut visitor = Visitor::new(encoder, proc_def_id);
    let initial_state = FoldUnfoldState::new();
    let shaped_procedure = visitor.infer_procedure(procedure, initial_state)?;
    visitor.cancel_crash_graphviz();
    if config::dump_debug_info() {
        let source_filename = encoder.env().name.source_file_name();
        prusti_common::report::log::report_with_writer(
            "graphviz_method_after_foldunfold",
            format!("{}.{}.dot", source_filename, shaped_procedure.name),
            |writer| shaped_procedure.to_graphviz(writer).unwrap(),
        );
    }
    Ok(shaped_procedure)
}
