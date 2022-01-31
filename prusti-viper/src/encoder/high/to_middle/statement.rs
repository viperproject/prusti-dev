use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use vir_crate::{
    high as vir_high, middle as vir_mid,
    middle::operations::{ToMiddleExpression, ToMiddlePredicate, ToMiddleStatementLowerer},
};

impl<'v, 'tcx> ToMiddleStatementLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn to_middle_statement_position(
        &self,
        position: vir_high::Position,
    ) -> SpannedEncodingResult<vir_mid::Position> {
        assert!(!position.is_default());
        Ok(position)
    }

    fn to_middle_statement_expression(
        &self,
        expression: vir_high::Expression,
    ) -> SpannedEncodingResult<vir_mid::Expression> {
        expression.to_middle_expression(self)
    }

    fn to_middle_statement_predicate(
        &self,
        predicate: vir_high::Predicate,
    ) -> SpannedEncodingResult<vir_mid::Predicate> {
        predicate.to_middle_predicate(self)
    }
}
