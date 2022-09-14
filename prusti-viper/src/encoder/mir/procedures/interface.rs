use crate::encoder::{
    errors::SpannedEncodingResult,
    mir::{
        procedures::{encoder::ProcedureEncodingKind, passes},
        spans::SpanInterface,
    },
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
    ) -> SpannedEncodingResult<Vec<vir_high::ProcedureDecl>>;
    fn get_span_of_location(&self, mir: &mir::Body<'tcx>, location: mir::Location) -> Span;
}

impl<'v, 'tcx: 'v> MirProcedureEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    #[tracing::instrument(level = "debug", skip(self))]
    fn encode_procedure_core_proof_high(
        &mut self,
        proc_def_id: DefId,
        check_mode: CheckMode,
    ) -> SpannedEncodingResult<Vec<vir_high::ProcedureDecl>> {
        let procedure = super::encoder::encode_procedure(
            self,
            proc_def_id,
            check_mode,
            ProcedureEncodingKind::Regular,
        )?;
        let procedure = passes::run_passes(self, procedure)?;
        let mut procedures = Vec::new();
        if check_mode.check_core_proof() && !self.env().query.is_drop_method_impl(proc_def_id) {
            let postcondition_check = super::encoder::encode_procedure(
                self,
                proc_def_id,
                check_mode,
                ProcedureEncodingKind::PostconditionFrameCheck,
            )?;
            procedures.push(postcondition_check);
        }
        assert!(
            self.mir_procedure_encoder_state
                .encoded_procedure_def_ids
                .insert(procedure.name.clone(), (proc_def_id, check_mode))
                .is_none(),
            "The procedure was encoded twice: {proc_def_id:?}"
        );
        procedures.push(procedure);
        Ok(procedures)
    }
    fn get_span_of_location(&self, mir: &mir::Body<'tcx>, location: mir::Location) -> Span {
        self.get_mir_location_span(mir, location)
    }
}
