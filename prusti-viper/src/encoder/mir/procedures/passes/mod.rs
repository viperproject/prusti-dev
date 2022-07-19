use crate::encoder::{errors::SpannedEncodingResult, Encoder};
use prusti_common::config;
use vir_crate::{
    common::graphviz::ToGraphviz,
    high::{self as vir_high},
};

mod assertions;
mod loop_desugaring;

pub(super) use self::{assertions::propagate_assertions_back, loop_desugaring::desugar_loops};

fn log_pass<'v, 'tcx: 'v>(
    encoder: &mut Encoder<'v, 'tcx>,
    procedure: &vir_high::ProcedureDecl,
    pass_name: &str,
    is_before: bool,
) {
    if config::dump_debug_info() {
        let source_filename = encoder.env().source_file_name();
        let is_before = if is_before { "before" } else { "after" };
        prusti_common::report::log::report_with_writer(
            &format!("graphviz_method_pass_{}_{}", pass_name, is_before),
            format!("{}.{}.dot", source_filename, procedure.name),
            |writer| procedure.to_graphviz(writer).unwrap(),
        );
    }
}

macro run_pass($pass:ident( $encoder:ident, $procedure:ident )) {
    log_pass($encoder, &$procedure, stringify!($pass), true);
    $procedure = $pass($encoder, $procedure)?;
    log_pass($encoder, &$procedure, stringify!($pass), false);
}

pub(super) fn run_passes<'v, 'tcx: 'v>(
    encoder: &mut Encoder<'v, 'tcx>,
    mut procedure: vir_high::ProcedureDecl,
) -> SpannedEncodingResult<vir_high::ProcedureDecl> {
    run_pass!(desugar_loops(encoder, procedure));
    run_pass!(propagate_assertions_back(encoder, procedure));
    Ok(procedure)
}
