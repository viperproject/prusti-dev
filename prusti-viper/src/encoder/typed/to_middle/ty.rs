use crate::encoder::errors::SpannedEncodingError;
use vir_crate::{
    middle as vir_mid,
    middle::operations::{
        MiddleToTypedType, MiddleToTypedTypeUpperer, TypedToMiddleExpression,
        TypedToMiddleTypeLowerer,
    },
    typed::{self as vir_typed},
};

impl<'v, 'tcx> TypedToMiddleTypeLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn typed_to_middle_type_expression(
        &self,
        expression: vir_typed::Expression,
    ) -> Result<vir_mid::Expression, Self::Error> {
        expression.typed_to_middle_expression(self)
    }
}

impl<'v, 'tcx> MiddleToTypedTypeUpperer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn middle_to_typed_type_expression(
        &self,
        expression: vir_mid::Expression,
    ) -> Result<vir_typed::Expression, Self::Error> {
        match expression {
            vir_mid::Expression::Local(local) => Ok(vir_typed::Expression::local(
                vir_typed::VariableDecl::new(
                    local.variable.name,
                    local.variable.ty.middle_to_typed_type(self)?,
                ),
                local.position,
            )),
            vir_mid::Expression::Constant(constant) => {
                let value = match constant.value {
                    vir_mid::expression::ConstantValue::Bool(value) => {
                        vir_typed::expression::ConstantValue::Bool(value)
                    }
                    vir_mid::expression::ConstantValue::Int(value) => {
                        vir_typed::expression::ConstantValue::Int(value)
                    }
                    vir_mid::expression::ConstantValue::BigInt(value) => {
                        vir_typed::expression::ConstantValue::BigInt(value)
                    }
                    vir_mid::expression::ConstantValue::String(value) => {
                        vir_typed::expression::ConstantValue::String(value)
                    }
                    vir_mid::expression::ConstantValue::Float(value) => {
                        vir_typed::expression::ConstantValue::Float(value)
                    }
                    vir_mid::expression::ConstantValue::FnPtr => {
                        vir_typed::expression::ConstantValue::FnPtr
                    }
                };
                Ok(vir_typed::Expression::constant(
                    value,
                    constant.ty.middle_to_typed_type(self)?,
                    constant.position,
                ))
            }
            _ => unreachable!("{expression}"),
        }
    }
}
