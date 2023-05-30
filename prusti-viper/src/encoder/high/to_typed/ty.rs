use crate::encoder::{
    errors::SpannedEncodingError, high::to_typed::types::HighToTypedTypeEncoderInterface,
};
use vir_crate::{
    high as vir_high,
    typed::{
        self as vir_typed,
        operations::{
            HighToTypedExpression, HighToTypedType, HighToTypedTypeLowerer, TypedToHighType,
            TypedToHighTypeUpperer,
        },
    },
};

impl<'v, 'tcx> HighToTypedTypeLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn high_to_typed_type_type(
        &mut self,
        ty: vir_high::Type,
    ) -> Result<vir_typed::Type, Self::Error> {
        self.type_from_high_to_typed(ty)
    }

    fn high_to_typed_type_type_tuple(
        &mut self,
        ty: vir_high::ty::Tuple,
    ) -> Result<vir_typed::ty::Type, Self::Error> {
        let arguments = ty.arguments.high_to_typed_type(self)?;
        Ok(vir_typed::Type::struct_(
            // self.generate_tuple_name(&arguments)?,
            "Tuple".to_string(),
            arguments,
            ty.lifetimes.high_to_typed_type(self)?,
        ))
    }

    fn high_to_typed_type_type_never(
        &mut self,
    ) -> Result<vir_crate::typed::ast::ty::Type, Self::Error> {
        Ok(vir_typed::Type::struct_(
            "Never".to_string(),
            Vec::new(),
            Vec::new(),
        ))
    }

    fn high_to_typed_type_expression(
        &mut self,
        expression: vir_high::Expression,
    ) -> Result<vir_typed::Expression, Self::Error> {
        expression.high_to_typed_expression(self)
    }

    fn high_to_typed_type_type_union(
        &mut self,
        ty: vir_high::ty::Union,
    ) -> Result<vir_typed::ty::Type, Self::Error> {
        let arguments = ty.arguments.high_to_typed_type(self)?;
        Ok(vir_typed::Type::enum_(
            ty.name,
            vir_typed::ty::EnumSafety::Union,
            arguments,
            ty.variant
                .map(|variant| variant.high_to_typed_expression(self))
                .transpose()?,
            ty.lifetimes.high_to_typed_type(self)?,
        ))
    }

    fn high_to_typed_type_enum(
        &mut self,
        ty: vir_high::ty::Enum,
    ) -> Result<vir_typed::ty::Enum, Self::Error> {
        let arguments = ty.arguments.high_to_typed_type(self)?;
        Ok(vir_typed::ty::Enum {
            name: ty.name,
            safety: vir_typed::ty::EnumSafety::Enum,
            arguments,
            variant: ty
                .variant
                .map(|variant| variant.high_to_typed_expression(self))
                .transpose()?,
            lifetimes: ty.lifetimes.high_to_typed_type(self)?,
        })
    }
}

impl<'v, 'tcx> TypedToHighTypeUpperer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn typed_to_high_type_expression(
        &mut self,
        expression: vir_typed::Expression,
    ) -> Result<vir_high::Expression, Self::Error> {
        match expression {
            vir_typed::Expression::Local(local) => Ok(vir_high::Expression::local(
                vir_high::VariableDecl::new(
                    local.variable.name,
                    local.variable.ty.typed_to_high_type(self)?,
                ),
                local.position,
            )),
            vir_typed::Expression::Constant(constant) => {
                let value = match constant.value {
                    vir_typed::expression::ConstantValue::Bool(value) => {
                        vir_high::expression::ConstantValue::Bool(value)
                    }
                    vir_typed::expression::ConstantValue::Int(value) => {
                        vir_high::expression::ConstantValue::Int(value)
                    }
                    vir_typed::expression::ConstantValue::BigInt(value) => {
                        vir_high::expression::ConstantValue::BigInt(value)
                    }
                    vir_typed::expression::ConstantValue::Float(value) => {
                        vir_high::expression::ConstantValue::Float(value)
                    }
                    vir_typed::expression::ConstantValue::String(value) => {
                        vir_high::expression::ConstantValue::String(value)
                    }
                    vir_typed::expression::ConstantValue::FnPtr => {
                        vir_high::expression::ConstantValue::FnPtr
                    }
                };
                Ok(vir_high::Expression::constant(
                    value,
                    constant.ty.typed_to_high_type(self)?,
                    constant.position,
                ))
            }
            _ => unreachable!("{expression}"),
        }
    }

    fn typed_to_high_type_enum(
        &mut self,
        ty: vir_crate::typed::ast::ty::Enum,
    ) -> Result<vir_crate::high::ast::ty::Enum, Self::Error> {
        match ty.safety {
            vir_typed::ty::EnumSafety::Enum => todo!(),
            vir_typed::ty::EnumSafety::Union => todo!(),
        }
    }
}
