use crate::encoder::errors::SpannedEncodingError;
use vir_crate::{
    high as vir_high, middle as vir_mid,
    middle::operations::{ToMiddleExpression, ToMiddlePredicateLowerer},
};

impl<'v, 'tcx> ToMiddlePredicateLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn to_middle_predicate_position(&self, position: vir_high::Position) -> vir_mid::Position {
        position.into()
    }

    fn to_middle_predicate_expression(
        &self,
        expression: vir_high::Expression,
    ) -> vir_mid::Expression {
        expression.to_middle_expression(self)
    }
}
