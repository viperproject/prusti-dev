use crate::encoder::{
    errors::SpannedEncodingResult, mir::type_layouts::MirTypeLayoutsEncoderInterface,
};
use rustc_middle::ty;
use vir_crate::middle::{self as vir_mid, operations::ToMiddleExpression};

pub(crate) trait HighTypeLayoutsEncoderInterface<'tcx> {
    fn encode_type_size_expression_mid(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_mid::Expression>;
}

impl<'v, 'tcx: 'v> HighTypeLayoutsEncoderInterface<'tcx>
    for super::super::super::Encoder<'v, 'tcx>
{
    fn encode_type_size_expression_mid(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<vir_mid::Expression> {
        let expression = self.encode_type_size_expression(ty)?;
        expression.to_middle_expression(self)
    }
}
