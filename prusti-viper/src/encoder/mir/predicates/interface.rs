use prusti_rustc_interface::middle::mir;
use vir_crate::high as vir_high;

use crate::encoder::{
    errors::SpannedEncodingResult,
    mir::{places::PlacesEncoderInterface, type_layouts::MirTypeLayoutsEncoderInterface},
};

pub(crate) trait MirPredicateEncoderInterface<'tcx> {
    fn encode_memory_block_for_local(
        &self,
        mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<vir_high::Predicate>;
    fn encode_memory_block_drop_for_local(
        &self,
        mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<vir_high::Predicate>;
}

impl<'v, 'tcx: 'v> MirPredicateEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_memory_block_for_local(
        &self,
        mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<vir_high::Predicate> {
        let variable = self.encode_local_high(mir, local)?;
        let mir_type = self.get_local_type(mir, local)?;
        let size = self.encode_type_size_expression(mir_type)?;
        Ok(vir_high::Predicate::memory_block_stack(
            variable.into(),
            size,
            Default::default(), // FIXME: Set proper error reporting.
        ))
    }
    fn encode_memory_block_drop_for_local(
        &self,
        mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<vir_high::Predicate> {
        let variable = self.encode_local_high(mir, local)?;
        let mir_type = self.get_local_type(mir, local)?;
        let size = self.encode_type_size_expression(mir_type)?;
        Ok(vir_high::Predicate::memory_block_stack_drop(
            variable.into(),
            size,
            Default::default(), // FIXME: Set proper error reporting.
        ))
    }
}
