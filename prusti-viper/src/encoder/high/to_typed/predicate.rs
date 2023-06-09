use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use vir_crate::{
    high as vir_high, typed as vir_typed,
    typed::operations::{HighToTypedExpression, HighToTypedPredicateLowerer},
};

impl<'v, 'tcx> HighToTypedPredicateLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn high_to_typed_predicate_position(
        &mut self,
        position: vir_high::Position,
    ) -> SpannedEncodingResult<vir_typed::Position> {
        Ok(position)
    }

    fn high_to_typed_predicate_expression(
        &mut self,
        expression: vir_high::Expression,
    ) -> SpannedEncodingResult<vir_typed::Expression> {
        expression.high_to_typed_expression(self)
    }

    fn high_to_typed_predicate_lifetime_const(
        &mut self,
        lifetime_const: vir_high::ty::LifetimeConst,
    ) -> SpannedEncodingResult<vir_typed::ty::LifetimeConst> {
        Ok(vir_typed::ty::LifetimeConst {
            name: lifetime_const.name,
        })
    }

    fn high_to_typed_predicate_trigger(
        &mut self,
        trigger: vir_high::Trigger,
    ) -> Result<vir_typed::Trigger, Self::Error> {
        trigger.high_to_typed_expression(self)
    }

    fn high_to_typed_predicate_variable_decl(
        &mut self,
        variable: vir_high::VariableDecl,
    ) -> Result<vir_typed::VariableDecl, Self::Error> {
        variable.high_to_typed_expression(self)
    }
}
