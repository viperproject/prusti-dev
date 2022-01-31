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
            ty: self.to_middle_expression_type(decl.ty)?,
        })
    }

    fn to_middle_type_decl_expression(
        &self,
        expression: vir_high::Expression,
    ) -> Result<vir_mid::Expression, Self::Error> {
        expression.to_middle_expression(self)
    }
}
