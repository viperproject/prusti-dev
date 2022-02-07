use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use vir_crate::{
    high as vir_high, middle as vir_mid,
    middle::operations::{ToMiddleExpression, ToMiddlePredicateLowerer},
};

impl<'v, 'tcx> ToMiddlePredicateLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn to_middle_predicate_position(
        &self,
        position: vir_high::Position,
    ) -> SpannedEncodingResult<vir_mid::Position> {
        Ok(position)
    }

    fn to_middle_predicate_expression(
        &self,
        expression: vir_high::Expression,
    ) -> SpannedEncodingResult<vir_mid::Expression> {
        expression.to_middle_expression(self)
    }
}
