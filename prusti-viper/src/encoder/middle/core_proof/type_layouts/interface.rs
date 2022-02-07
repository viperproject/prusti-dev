use crate::encoder::{
    errors::SpannedEncodingResult,
    high::{type_layouts::HighTypeLayoutsEncoderInterface, types::HighTypeEncoderInterface},
    middle::core_proof::{into_low::IntoLowInterface, lowerer::Lowerer, snapshots::IntoSnapshot},
};
use vir_crate::{low as vir_low, middle as vir_mid};

pub(in super::super) trait TypeLayoutsInterface {
    fn size_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn encode_type_size_expression(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> TypeLayoutsInterface for Lowerer<'p, 'v, 'tcx> {
    fn size_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        let usize = vir_mid::Type::Int(vir_mid::ty::Int::Usize);
        usize.create_snapshot(self)
    }
    fn encode_type_size_expression(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mir_type = self.encoder.decode_type_mid(ty)?;
        let size = self.encoder.encode_type_size_expression_mid(mir_type)?;
        self.lower_expression(size)
    }
}
