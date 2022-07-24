use crate::encoder::{
    errors::SpannedEncodingResult,
    mir::{constants::ConstantsEncoderInterface, types::MirTypeEncoderInterface},
};
use prusti_rustc_interface::middle::ty;
use vir_crate::high as vir_high;

pub(crate) trait MirTypeLayoutsEncoderInterface<'tcx> {
    /// Returns the size of memory block containing `count` consequative
    /// elements of `ty` elements. Note that there is no guarantee for `size(c,
    /// ty) == c * size(c, ty)` because of padding.
    fn encode_type_size_expression_with_reps(
        &self,
        count: vir_high::Expression,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;
    fn encode_type_size_expression(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;
}

impl<'v, 'tcx: 'v> MirTypeLayoutsEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_type_size_expression_with_reps(
        &self,
        count: vir_high::Expression,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let encoded_ty = self.encode_type_high(ty)?;
        let usize = vir_high::Type::Int(vir_high::ty::Int::Usize);
        let function_call = vir_high::Expression::builtin_func_app_no_pos(
            vir_high::BuiltinFunc::Size,
            vec![encoded_ty],
            vec![count],
            usize,
        );
        Ok(function_call)
    }

    fn encode_type_size_expression(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        match ty.kind() {
            ty::TyKind::Array(elem_ty, size) => {
                let array_len: usize = self.compute_array_len(*size).try_into().unwrap();
                self.encode_type_size_expression_with_reps(array_len.into(), *elem_ty)
            }
            _ => self.encode_type_size_expression_with_reps(1usize.into(), ty),
        }
    }
}
