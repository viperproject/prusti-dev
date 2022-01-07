use crate::encoder::errors::SpannedEncodingResult;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_span::Span;
use vir_crate::high::cfg;

pub(crate) trait MirProcedureEncoderInterface<'tcx> {
    fn encode_procedure_core_proof_high(
        &mut self,
        proc_def_id: DefId,
    ) -> SpannedEncodingResult<cfg::ProcedureDecl>;
    fn get_span_of_location(&self, mir: &mir::Body<'tcx>, location: mir::Location) -> Span;
}

impl<'v, 'tcx: 'v> MirProcedureEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_procedure_core_proof_high(
        &mut self,
        proc_def_id: DefId,
    ) -> SpannedEncodingResult<cfg::ProcedureDecl> {
        let procedure = super::encoder::encode_procedure(self, proc_def_id)?;
        Ok(procedure)
    }
    fn get_span_of_location(&self, mir: &mir::Body<'tcx>, location: mir::Location) -> Span {
        mir.source_info(location).span
    }
}
