use crate::encoder::{
    errors::SpannedEncodingError, high::to_typed::types::HighToTypedTypeEncoderInterface,
};
use vir_crate::{
    high as vir_high,
    typed::{
        self as vir_typed,
        operations::{HighToTypedExpression, HighToTypedType, HighToTypedTypeDeclLowerer},
    },
};

impl<'v, 'tcx> HighToTypedTypeDeclLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn high_to_typed_type_decl_type(
        &mut self,
        ty: vir_high::Type,
    ) -> Result<vir_typed::Type, Self::Error> {
        ty.high_to_typed_type(self)
    }

    fn high_to_typed_type_decl_uniqueness(
        &mut self,
        uniqueness: vir_high::ty::Uniqueness,
    ) -> Result<vir_typed::ty::Uniqueness, Self::Error> {
        Ok(match uniqueness {
            vir_high::ty::Uniqueness::Unique => vir_typed::ty::Uniqueness::Unique,
            vir_high::ty::Uniqueness::Shared => vir_typed::ty::Uniqueness::Shared,
        })
    }

    fn high_to_typed_type_decl_field_decl(
        &mut self,
        decl: vir_high::FieldDecl,
    ) -> Result<vir_typed::FieldDecl, Self::Error> {
        decl.high_to_typed_expression(self)
    }

    fn high_to_typed_type_decl_discriminant_value(
        &mut self,
        value: vir_high::DiscriminantValue,
    ) -> Result<vir_typed::DiscriminantValue, Self::Error> {
        Ok(value)
    }

    fn high_to_typed_type_decl_discriminant_range(
        &mut self,
        range: vir_high::DiscriminantRange,
    ) -> Result<vir_typed::DiscriminantRange, Self::Error> {
        Ok(range)
    }

    fn high_to_typed_type_decl_expression(
        &mut self,
        expression: vir_high::Expression,
    ) -> Result<vir_typed::Expression, Self::Error> {
        expression.high_to_typed_expression(self)
    }

    fn high_to_typed_type_decl_type_decl_tuple(
        &mut self,
        decl: vir_high::type_decl::Tuple,
    ) -> Result<vir_typed::TypeDecl, Self::Error> {
        let arguments = decl.arguments.high_to_typed_type(self)?;
        Ok(vir_typed::TypeDecl::struct_(
            self.generate_tuple_name(&arguments)?,
            arguments
                .into_iter()
                .enumerate()
                .map(|(index, ty)| vir_typed::FieldDecl::new(format!("tuple_{}", index), index, ty))
                .collect(),
        ))
    }
}
