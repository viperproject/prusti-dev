use crate::encoder::{
    errors::SpannedEncodingResult, high::procedures::HighProcedureEncoderInterface,
    mir::specifications::SpecificationsInterface,
};
use log::debug;
use rustc_hir::def_id::DefId;
use vir_crate::low::{self as vir_low};

#[derive(Default)]
pub(crate) struct MidCoreProofEncoderState {
    encoded_programs: Vec<vir_low::Program>,
}

pub(crate) trait MidCoreProofEncoderInterface<'tcx> {
    fn encode_lifetimes_core_proof(&mut self, proc_def_id: DefId) -> SpannedEncodingResult<()>;
    fn take_core_proof_programs(&mut self) -> Vec<vir_low::Program>;
}

impl<'v, 'tcx: 'v> MidCoreProofEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_lifetimes_core_proof(&mut self, proc_def_id: DefId) -> SpannedEncodingResult<()> {
        if self.is_trusted(proc_def_id, None) {
            debug!(
                "Trusted procedure will not be encoded or verified: {:?}",
                proc_def_id
            );
            return Ok(());
        }
        let procedure = self.encode_procedure_core_proof(proc_def_id)?;
        let super::lowerer::LoweringResult {
            procedure,
            domains,
            functions,
            predicates,
            methods,
        } = super::lowerer::lower_procedure(self, procedure)?;
        let program = vir_low::Program {
            name: self.env().get_absolute_item_name(proc_def_id),
            procedures: vec![procedure],
            domains,
            predicates,
            functions,
            methods,
        };
        self.mid_core_proof_encoder_state
            .encoded_programs
            .push(program);
        Ok(())
    }
    fn take_core_proof_programs(&mut self) -> Vec<vir_low::Program> {
        std::mem::take(&mut self.mid_core_proof_encoder_state.encoded_programs)
    }
}
