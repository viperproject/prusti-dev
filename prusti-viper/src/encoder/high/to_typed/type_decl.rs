use crate::encoder::{
    errors::SpannedEncodingError, high::to_typed::types::HighToTypedTypeEncoderInterface,
};
use vir_crate::{
    high as vir_high,
    typed::{
        self as vir_typed,
        operations::{
            HighToTypedExpression, HighToTypedType, HighToTypedTypeDecl, HighToTypedTypeDeclLowerer,
        },
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
            decl.lifetimes.high_to_typed_type(self)?,
            decl.const_parameters.high_to_typed_expression(self)?,
            None,
            arguments
                .into_iter()
                .enumerate()
                .map(|(index, ty)| vir_typed::FieldDecl::new(format!("tuple_{index}"), index, ty))
                .collect(),
            None,
            Default::default(),
        ))
    }

    fn high_to_typed_type_decl_type_decl_never(
        &mut self,
    ) -> Result<vir_typed::TypeDecl, Self::Error> {
        Ok(vir_typed::TypeDecl::struct_(
            "Never".to_owned(),
            Vec::new(),
            Vec::new(),
            Some(vec![false.into()]),
            Vec::new(),
            None,
            Default::default(),
        ))
    }

    fn high_to_typed_type_decl_variable_decl(
        &mut self,
        variable: vir_high::VariableDecl,
    ) -> Result<vir_typed::VariableDecl, Self::Error> {
        variable.high_to_typed_expression(self)
    }

    fn high_to_typed_type_decl_lifetime_const(
        &mut self,
        lifetime: vir_high::ty::LifetimeConst,
    ) -> Result<vir_typed::ty::LifetimeConst, Self::Error> {
        lifetime.high_to_typed_type(self)
    }

    fn high_to_typed_type_decl_type_decl_slice(
        &mut self,
        decl: vir_high::type_decl::Slice,
    ) -> Result<vir_typed::TypeDecl, Self::Error> {
        Ok(vir_typed::TypeDecl::Array(vir_typed::type_decl::Array {
            lifetimes: decl.lifetimes.high_to_typed_type(self)?,
            const_parameters: decl.const_parameters.high_to_typed_expression(self)?,
            element_type: decl.element_type.high_to_typed_type(self)?,
        }))
    }

    fn high_to_typed_type_decl_array(
        &mut self,
        decl: vir_high::type_decl::Array,
    ) -> Result<vir_typed::type_decl::Array, Self::Error> {
        Ok(vir_typed::type_decl::Array {
            lifetimes: decl.lifetimes.high_to_typed_type(self)?,
            const_parameters: decl.const_parameters.high_to_typed_expression(self)?,
            element_type: decl.element_type.high_to_typed_type(self)?,
        })
    }

    fn high_to_typed_type_decl_type_decl_union(
        &mut self,
        decl: vir_high::type_decl::Union,
    ) -> Result<vir_typed::TypeDecl, Self::Error> {
        Ok(vir_typed::TypeDecl::enum_(
            decl.name,
            vir_typed::ty::EnumSafety::Union,
            decl.arguments.high_to_typed_type(self)?,
            decl.lifetimes.high_to_typed_type(self)?,
            decl.const_parameters.high_to_typed_expression(self)?,
            decl.discriminant_type.high_to_typed_type(self)?,
            decl.discriminant_bounds,
            decl.discriminant_values,
            decl.variants.high_to_typed_type_decl(self)?,
        ))
    }

    fn high_to_typed_type_decl_enum(
        &mut self,
        decl: vir_high::type_decl::Enum,
    ) -> Result<vir_typed::type_decl::Enum, Self::Error> {
        Ok(vir_typed::type_decl::Enum {
            name: decl.name,
            safety: vir_typed::ty::EnumSafety::Enum,
            arguments: decl.arguments.high_to_typed_type(self)?,
            lifetimes: decl.lifetimes.high_to_typed_type(self)?,
            const_parameters: decl.const_parameters.high_to_typed_expression(self)?,
            discriminant_type: decl.discriminant_type.high_to_typed_type(self)?,
            discriminant_bounds: decl.discriminant_bounds,
            discriminant_values: decl.discriminant_values,
            variants: decl.variants.high_to_typed_type_decl(self)?,
        })
    }

    fn high_to_typed_type_decl_position(
        &mut self,
        position: vir_high::Position,
    ) -> Result<vir_typed::Position, Self::Error> {
        Ok(position)
    }
}
