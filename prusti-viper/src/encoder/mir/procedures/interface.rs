use crate::encoder::{
    errors::SpannedEncodingResult,
    mir::{procedures::passes, spans::SpanInterface},
};
use prusti_rustc_interface::{hir::def_id::DefId, middle::mir, span::Span};
use rustc_hash::FxHashMap;
use vir_crate::{common::check_mode::CheckMode, high as vir_high};

#[derive(Default)]
pub(crate) struct MirProcedureEncoderState {
    /// Mapping from the encoding procedure name to its definition ID.
    encoded_procedure_def_ids: FxHashMap<String, (DefId, CheckMode)>,
}

pub(crate) trait MirProcedureEncoderInterface<'tcx> {
    fn encode_procedure_core_proof_high(
        &mut self,
        proc_def_id: DefId,
        check_mode: CheckMode,
    ) -> SpannedEncodingResult<vir_high::ProcedureDecl>;
    fn get_span_of_location(&self, mir: &mir::Body<'tcx>, location: mir::Location) -> Span;
    fn decode_procedure_def_id(&self, procedure_name: &str) -> DefId;
}

impl<'v, 'tcx: 'v> MirProcedureEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_procedure_core_proof_high(
        &mut self,
        proc_def_id: DefId,
        check_mode: CheckMode,
    ) -> SpannedEncodingResult<vir_high::ProcedureDecl> {
        let procedure = super::encoder::encode_procedure(self, proc_def_id, check_mode)?;
        let procedure = passes::run_passes(self, procedure)?;
        assert!(
            self.mir_procedure_encoder_state
                .encoded_procedure_def_ids
                .insert(procedure.name.clone(), (proc_def_id, check_mode))
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
        self.mir_procedure_encoder_state.encoded_procedure_def_ids[procedure_name].0
    }
}
