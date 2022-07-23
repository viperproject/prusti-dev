use crate::encoder::{
    errors::SpannedEncodingResult, mir::procedures::MirProcedureEncoderInterface,
};
use log::debug;
use prusti_rustc_interface::hir::def_id::DefId;
use vir_crate::{common::check_mode::CheckMode, middle as vir_mid};

pub(crate) trait HighProcedureEncoderInterface<'tcx> {
    fn encode_procedure_core_proof(
        &mut self,
        proc_def_id: DefId,
        check_mode: CheckMode,
    ) -> SpannedEncodingResult<vir_mid::ProcedureDecl>;
}

impl<'v, 'tcx: 'v> HighProcedureEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_procedure_core_proof(
        &mut self,
        proc_def_id: DefId,
        check_mode: CheckMode,
    ) -> SpannedEncodingResult<vir_mid::ProcedureDecl> {
        let procedure_high = self.encode_procedure_core_proof_high(proc_def_id, check_mode)?;
        debug!("procedure_high:\n{}", procedure_high);
        let procedure =
            super::inference::infer_shape_operations(self, proc_def_id, procedure_high)?;
        Ok(procedure)
    }
}
