use crate::encoder::errors::SpannedEncodingError;
use vir_crate::{
    middle as vir_mid,
    middle::operations::{
        TypedToMiddleExpression, TypedToMiddleType, TypedToMiddleTypeDeclLowerer,
    },
    typed as vir_typed,
};

impl<'v, 'tcx> TypedToMiddleTypeDeclLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn typed_to_middle_type_decl_type(
        &self,
        ty: vir_typed::Type,
    ) -> Result<vir_mid::Type, Self::Error> {
        ty.typed_to_middle_type(self)
    }

    fn typed_to_middle_type_decl_uniqueness(
        &self,
        ty: vir_typed::ty::Uniqueness,
    ) -> Result<vir_mid::ty::Uniqueness, Self::Error> {
        ty.typed_to_middle_type(self)
    }

    fn typed_to_middle_type_decl_field_decl(
        &self,
        decl: vir_typed::FieldDecl,
    ) -> Result<vir_mid::FieldDecl, Self::Error> {
        decl.typed_to_middle_expression(self)
    }

    fn typed_to_middle_type_decl_discriminant_value(
        &self,
        value: vir_typed::DiscriminantValue,
    ) -> Result<vir_mid::DiscriminantValue, Self::Error> {
        Ok(value)
    }

    fn typed_to_middle_type_decl_discriminant_range(
        &self,
        range: vir_typed::DiscriminantRange,
    ) -> Result<vir_mid::DiscriminantRange, Self::Error> {
        Ok(range)
    }

    fn typed_to_middle_type_decl_expression(
        &self,
        expression: vir_typed::Expression,
    ) -> Result<vir_mid::Expression, Self::Error> {
        expression.typed_to_middle_expression(self)
    }

    fn typed_to_middle_type_decl_lifetime_const(
        &self,
        lifetime: vir_typed::ty::LifetimeConst,
    ) -> Result<vir_mid::ty::LifetimeConst, Self::Error> {
        lifetime.typed_to_middle_type(self)
    }

    fn typed_to_middle_type_decl_variable_decl(
        &self,
        variable: vir_typed::VariableDecl,
    ) -> Result<vir_mid::VariableDecl, Self::Error> {
        variable.typed_to_middle_expression(self)
    }

    fn typed_to_middle_type_decl_enum_safety(
        &self,
        safety: vir_typed::ty::EnumSafety,
    ) -> Result<vir_mid::ty::EnumSafety, Self::Error> {
        Ok(match safety {
            vir_typed::ty::EnumSafety::Enum => vir_mid::ty::EnumSafety::Enum,
            vir_typed::ty::EnumSafety::Union => vir_mid::ty::EnumSafety::Union,
        })
    }

    fn typed_to_middle_type_decl_position(
        &self,
        position: vir_typed::Position,
    ) -> Result<vir_mid::Position, Self::Error> {
        Ok(position)
    }
}
