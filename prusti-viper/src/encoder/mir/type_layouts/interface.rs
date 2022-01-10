use rustc_middle::{mir, ty};
use vir_crate::high as vir_high;

use crate::encoder::{
    errors::SpannedEncodingResult,
    mir::{places::PlacesEncoderInterface, types::MirTypeEncoderInterface},
};

pub(crate) trait MirTypeLayoutsEncoderInterface<'tcx> {
    fn encode_type_size_expression(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;
}

impl<'v, 'tcx: 'v> MirTypeLayoutsEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_type_size_expression(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let encoded_ty = self.encode_type_high(ty)?;
        // FIXME: Should use encode_builtin_function_use.
        let name = "size";
        Ok(vir_high::Expression::function_call(
            name,
            vec![encoded_ty],
            vec![],
            vir_high::ty::Type::Int(vir_high::ty::Int::Usize),
        ))
    }
}
