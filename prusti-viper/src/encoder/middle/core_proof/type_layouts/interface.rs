use crate::encoder::{
    errors::SpannedEncodingResult,
    high::{type_layouts::HighTypeLayoutsEncoderInterface, types::HighTypeEncoderInterface},
    middle::core_proof::{
        lowerer::Lowerer,
        snapshots::{IntoBuiltinMethodSnapshot, IntoProcedureSnapshot, IntoSnapshot},
    },
};
use vir_crate::{high as vir_high, low as vir_low, middle as vir_mid};

pub(in super::super) trait TypeLayoutsInterface {
    fn size_type_mid(&mut self) -> SpannedEncodingResult<vir_mid::Type>;
    fn size_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn size_constant(
        &mut self,
        value: impl Into<vir_mid::expression::ConstantValue>,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_type_size_expression(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> TypeLayoutsInterface for Lowerer<'p, 'v, 'tcx> {
    fn size_type_mid(&mut self) -> SpannedEncodingResult<vir_mid::Type> {
        Ok(vir_mid::Type::Int(vir_mid::ty::Int::Usize))
    }
    fn size_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.size_type_mid()?.to_snapshot(self)
    }
    fn size_constant(
        &mut self,
        value: impl Into<vir_mid::expression::ConstantValue>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        vir_mid::Expression::constant_no_pos(value.into(), self.size_type_mid()?)
            .to_procedure_snapshot(self)
    }
    fn encode_type_size_expression(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let size = match ty {
            vir_mid::Type::Array(array) => {
                // FIXME: Figure out how to avoid these magic variable names.
                // They are defined in extract_non_type_parameters_from_type.
                let array_length = vir_high::VariableDecl::new(
                    "array_length",
                    vir_high::Type::Int(vir_high::ty::Int::Usize),
                );
                let mir_type = self.encoder.decode_type_mid(&array.element_type)?;
                self.encoder
                    .encode_type_size_expression_mid(array_length.into(), mir_type)?
            }
            _ => {
                let mir_type = self.encoder.decode_type_mid(ty)?;
                self.encoder
                    .encode_type_size_expression_mid(1usize.into(), mir_type)?
            }
        };
        size.to_builtin_method_snapshot(self)
    }
}
