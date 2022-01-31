use crate::encoder::{
    errors::SpannedEncodingResult, mir::procedures::MirProcedureEncoderInterface,
};
use log::debug;
use rustc_hir::def_id::DefId;

use vir_crate::middle as vir_mid;

pub(crate) trait HighProcedureEncoderInterface<'tcx> {
    fn encode_procedure_core_proof(
        &mut self,
        proc_def_id: DefId,
    ) -> SpannedEncodingResult<vir_mid::ProcedureDecl>;
}

impl<'v, 'tcx: 'v> HighProcedureEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_procedure_core_proof(
        &mut self,
        proc_def_id: DefId,
    ) -> SpannedEncodingResult<vir_mid::ProcedureDecl> {
        let procedure_high = self.encode_procedure_core_proof_high(proc_def_id)?;
        debug!("procedure_high:\n{}", procedure_high);
        let procedure =
            super::inference::infer_shape_operations(self, proc_def_id, procedure_high)?;
        Ok(procedure)
    }
}
