use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use vir_crate::{
    high as vir_high, middle as vir_mid,
    middle::operations::{ToMiddleExpressionLowerer, ToMiddleType},
};

impl<'v, 'tcx> ToMiddleExpressionLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn to_middle_expression_position(
        &self,
        ty: vir_high::Position,
    ) -> SpannedEncodingResult<vir_mid::Position> {
        Ok(ty)
    }

    fn to_middle_expression_field_decl(
        &self,
        decl: vir_high::FieldDecl,
    ) -> SpannedEncodingResult<vir_mid::FieldDecl> {
        Ok(vir_mid::FieldDecl {
            name: decl.name,
            index: decl.index,
            ty: self.to_middle_expression_type(decl.ty)?,
        })
    }

    fn to_middle_expression_type(
        &self,
        ty: vir_high::Type,
    ) -> SpannedEncodingResult<vir_mid::Type> {
        ty.to_middle_type(self)
    }

    fn to_middle_expression_variable_decl(
        &self,
        decl: vir_high::VariableDecl,
    ) -> SpannedEncodingResult<vir_mid::VariableDecl> {
        Ok(vir_mid::VariableDecl {
            name: decl.name,
            ty: self.to_middle_expression_type(decl.ty)?,
        })
    }

    fn to_middle_expression_float_const(
        &self,
        constant: vir_high::expression::FloatConst,
    ) -> SpannedEncodingResult<vir_mid::expression::FloatConst> {
        Ok(match constant {
            vir_high::expression::FloatConst::F32(value) => {
                vir_mid::expression::FloatConst::F32(value)
            }
            vir_high::expression::FloatConst::F64(value) => {
                vir_mid::expression::FloatConst::F64(value)
            }
        })
    }

    fn to_middle_expression_variant_index(
        &self,
        variant_index: vir_high::ty::VariantIndex,
    ) -> SpannedEncodingResult<vir_mid::ty::VariantIndex> {
        Ok(vir_mid::ty::VariantIndex {
            index: variant_index.index,
        })
    }
}
