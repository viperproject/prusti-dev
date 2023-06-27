use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use vir_crate::{
    high as vir_high,
    typed::{
        self as vir_typed,
        operations::{HighToTypedExpressionLowerer, HighToTypedPredicateLowerer, HighToTypedType},
    },
};

impl<'v, 'tcx> HighToTypedExpressionLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn high_to_typed_expression_position(
        &mut self,
        ty: vir_high::Position,
    ) -> SpannedEncodingResult<vir_typed::Position> {
        Ok(ty)
    }

    fn high_to_typed_expression_field_decl(
        &mut self,
        decl: vir_high::FieldDecl,
    ) -> SpannedEncodingResult<vir_typed::FieldDecl> {
        Ok(vir_typed::FieldDecl {
            name: decl.name,
            index: decl.index,
            ty: self.high_to_typed_expression_type(decl.ty)?,
        })
    }

    fn high_to_typed_expression_type(
        &mut self,
        ty: vir_high::Type,
    ) -> SpannedEncodingResult<vir_typed::Type> {
        ty.high_to_typed_type(self)
    }

    fn high_to_typed_expression_variable_decl(
        &mut self,
        decl: vir_high::VariableDecl,
    ) -> SpannedEncodingResult<vir_typed::VariableDecl> {
        Ok(vir_typed::VariableDecl {
            name: decl.name,
            ty: self.high_to_typed_expression_type(decl.ty)?,
        })
    }

    fn high_to_typed_expression_float_const(
        &mut self,
        constant: vir_high::expression::FloatConst,
    ) -> SpannedEncodingResult<vir_typed::expression::FloatConst> {
        Ok(match constant {
            vir_high::expression::FloatConst::F32(value) => {
                vir_typed::expression::FloatConst::F32(value)
            }
            vir_high::expression::FloatConst::F64(value) => {
                vir_typed::expression::FloatConst::F64(value)
            }
        })
    }

    fn high_to_typed_expression_variant_index(
        &mut self,
        variant_index: vir_high::ty::VariantIndex,
    ) -> SpannedEncodingResult<vir_typed::ty::VariantIndex> {
        Ok(vir_typed::ty::VariantIndex {
            index: variant_index.index,
        })
    }

    fn high_to_typed_expression_predicate(
        &mut self,
        predicate: vir_high::Predicate,
    ) -> Result<vir_typed::Predicate, Self::Error> {
        self.high_to_typed_predicate_predicate(predicate)
    }
}
