use crate::encoder::errors::SpannedEncodingError;
use vir_crate::{
    high as vir_high, middle as vir_mid,
    middle::operations::{
        ToMiddleExpression, ToMiddleExpressionLowerer, ToMiddleType, ToMiddleTypeDeclLowerer,
    },
};

impl<'v, 'tcx> ToMiddleTypeDeclLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn to_middle_type_decl_type(&self, ty: vir_high::Type) -> Result<vir_mid::Type, Self::Error> {
        ty.to_middle_type(self)
    }

    fn to_middle_type_decl_field_decl(
        &self,
        decl: vir_high::FieldDecl,
    ) -> Result<vir_mid::FieldDecl, Self::Error> {
        Ok(vir_mid::FieldDecl {
            name: decl.name,
            index: decl.index,
            ty: self.to_middle_expression_type(decl.ty)?,
        })
    }

    fn to_middle_type_decl_expression(
        &self,
        expression: vir_high::Expression,
    ) -> Result<vir_mid::Expression, Self::Error> {
        expression.to_middle_expression(self)
    }

    fn to_middle_type_decl_discriminant_value(
        &self,
        value: vir_high::DiscriminantValue,
    ) -> Result<vir_mid::DiscriminantValue, Self::Error> {
        Ok(value)
    }

    fn to_middle_type_decl_discriminant_range(
        &self,
        range: vir_high::DiscriminantRange,
    ) -> Result<vir_mid::DiscriminantRange, Self::Error> {
        Ok(range)
    }

    fn to_middle_type_decl_uniqueness(
        &self,
        uniqueness: vir_high::ty::Uniqueness,
    ) -> Result<vir_mid::ty::Uniqueness, Self::Error> {
        Ok(match uniqueness {
            vir_high::ty::Uniqueness::Unique => vir_mid::ty::Uniqueness::Unique,
            vir_high::ty::Uniqueness::Shared => vir_mid::ty::Uniqueness::Shared,
        })
    }
}
