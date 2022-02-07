use super::super::lower::IntoPolymorphic;
use vir_crate::{
    high::{self as vir_high},
    polymorphic as vir_poly,
};

pub(crate) trait HighExpressionEncoderInterface {
    fn lower_into_poly(&self, expression: vir_high::Expression) -> vir_poly::Expr;
}

impl<'v, 'tcx: 'v> HighExpressionEncoderInterface for crate::encoder::encoder::Encoder<'v, 'tcx> {
    fn lower_into_poly(&self, expression: vir_high::Expression) -> vir_poly::Expr {
        expression.lower(self)
    }
}
