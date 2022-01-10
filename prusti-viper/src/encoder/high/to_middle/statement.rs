use crate::encoder::errors::SpannedEncodingError;
use vir_crate::{
    high as vir_high, middle as vir_mid,
    middle::operations::{ToMiddleExpression, ToMiddlePredicate, ToMiddleStatementLowerer},
};

impl<'v, 'tcx> ToMiddleStatementLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn to_middle_statement_position(&self, position: vir_high::Position) -> vir_mid::Position {
        position.into()
    }

    fn to_middle_statement_expression(
        &self,
        expression: vir_high::Expression,
    ) -> vir_mid::Expression {
        expression.to_middle_expression(self)
    }

    fn to_middle_statement_predicate(&self, predicate: vir_high::Predicate) -> vir_mid::Predicate {
        predicate.to_middle_predicate(self)
    }
}
