use crate::encoder::{
    errors::SpannedEncodingResult,
    high::{type_layouts::HighTypeLayoutsEncoderInterface, types::HighTypeEncoderInterface},
    middle::core_proof::{
        lowerer::Lowerer,
        snapshots::{IntoBuiltinMethodSnapshot, IntoProcedureSnapshot, IntoSnapshot},
    },
};
use vir_crate::{
    low as vir_low,
    middle::{self as vir_mid, operations::const_generics::WithConstArguments},
};

pub(in super::super) trait TypeLayoutsInterface {
    fn size_type_mid(&mut self) -> SpannedEncodingResult<vir_mid::Type>;
    fn size_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn size_constant(
        &mut self,
        value: impl Into<vir_mid::expression::ConstantValue>,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_type_size_expression2(
        &mut self,
        ty: &vir_mid::Type,
        generics: &impl WithConstArguments,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_type_padding_size_expression(
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
    fn encode_type_size_expression2(
        &mut self,
        ty: &vir_mid::Type,
        generics: &impl WithConstArguments,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let size_type = self.size_type_mid()?;
        let size = vir_mid::Expression::builtin_func_app_no_pos(
            vir_mid::BuiltinFunc::Size,
            vec![ty.clone()],
            generics.get_const_arguments(),
            size_type,
        );
        size.to_builtin_method_snapshot(self)
    }
    fn encode_type_padding_size_expression(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mir_type = self.encoder.decode_type_mid(ty)?;
        let size = self
            .encoder
            .encode_type_padding_size_expression_mid(mir_type)?;
        size.to_builtin_method_snapshot(self)
    }
}
