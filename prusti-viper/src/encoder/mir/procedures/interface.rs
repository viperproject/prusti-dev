use crate::encoder::{errors::SpannedEncodingResult, mir::spans::SpanInterface};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_span::Span;
use vir_crate::high::cfg;

#[derive(Default)]
pub(crate) struct MirProcedureEncoderState {
    /// Mapping from the encoding procedure name to its definition ID.
    encoded_procedure_def_ids: FxHashMap<String, DefId>,
}

pub(crate) trait MirProcedureEncoderInterface<'tcx> {
    fn encode_procedure_core_proof_high(
        &mut self,
        proc_def_id: DefId,
    ) -> SpannedEncodingResult<cfg::ProcedureDecl>;
    fn get_span_of_location(&self, mir: &mir::Body<'tcx>, location: mir::Location) -> Span;
    fn decode_procedure_def_id(&self, procedure_name: &str) -> DefId;
}

impl<'v, 'tcx: 'v> MirProcedureEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_procedure_core_proof_high(
        &mut self,
        proc_def_id: DefId,
    ) -> SpannedEncodingResult<cfg::ProcedureDecl> {
        let procedure = super::encoder::encode_procedure(self, proc_def_id)?;
        assert!(
            self.mir_procedure_encoder_state
                .encoded_procedure_def_ids
                .insert(procedure.name.clone(), proc_def_id)
                .is_none(),
            "The procedure was encoed twice: {:?}",
            proc_def_id
        );
        Ok(procedure)
    }
    fn get_span_of_location(&self, mir: &mir::Body<'tcx>, location: mir::Location) -> Span {
        self.get_mir_location_span(mir, location)
    }
    fn decode_procedure_def_id(&self, procedure_name: &str) -> DefId {
        self.mir_procedure_encoder_state.encoded_procedure_def_ids[procedure_name]
    }
}
