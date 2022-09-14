use crate::encoder::errors::SpannedEncodingError;
use vir_crate::{
    middle as vir_mid,
    middle::operations::{
        TypedToMiddleExpressionLowerer, TypedToMiddlePredicate, TypedToMiddleType,
    },
    typed as vir_typed,
};

impl<'v, 'tcx> TypedToMiddleExpressionLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn typed_to_middle_expression_position(
        &self,
        position: vir_typed::Position,
    ) -> Result<vir_mid::Position, Self::Error> {
        Ok(position)
    }

    fn typed_to_middle_expression_field_decl(
        &self,
        decl: vir_typed::FieldDecl,
    ) -> Result<vir_mid::FieldDecl, Self::Error> {
        Ok(vir_mid::FieldDecl {
            name: decl.name,
            index: decl.index,
            ty: self.typed_to_middle_expression_type(decl.ty)?,
        })
    }

    fn typed_to_middle_expression_type(
        &self,
        ty: vir_typed::Type,
    ) -> Result<vir_mid::Type, Self::Error> {
        ty.typed_to_middle_type(self)
    }

    fn typed_to_middle_expression_variable_decl(
        &self,
        decl: vir_typed::VariableDecl,
    ) -> Result<vir_mid::VariableDecl, Self::Error> {
        Ok(vir_mid::VariableDecl {
            name: decl.name,
            ty: self.typed_to_middle_expression_type(decl.ty)?,
        })
    }

    fn typed_to_middle_expression_float_const(
        &self,
        constant: vir_typed::expression::FloatConst,
    ) -> Result<vir_mid::expression::FloatConst, Self::Error> {
        Ok(match constant {
            vir_typed::expression::FloatConst::F32(value) => {
                vir_mid::expression::FloatConst::F32(value)
            }
            vir_typed::expression::FloatConst::F64(value) => {
                vir_mid::expression::FloatConst::F64(value)
            }
        })
    }

    fn typed_to_middle_expression_variant_index(
        &self,
        variant_index: vir_typed::ty::VariantIndex,
    ) -> Result<vir_mid::ty::VariantIndex, Self::Error> {
        Ok(vir_mid::ty::VariantIndex {
            index: variant_index.index,
        })
    }

    fn typed_to_middle_expression_predicate(
        &self,
        predicate: vir_typed::Predicate,
    ) -> Result<vir_mid::Predicate, Self::Error> {
        predicate.typed_to_middle_predicate(self)
    }
}
