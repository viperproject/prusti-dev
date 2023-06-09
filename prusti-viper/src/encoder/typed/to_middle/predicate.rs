use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use vir_crate::{
    middle as vir_mid,
    middle::operations::{TypedToMiddleExpression, TypedToMiddlePredicateLowerer},
    typed as vir_typed,
};

impl<'v, 'tcx> TypedToMiddlePredicateLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn typed_to_middle_predicate_position(
        &self,
        position: vir_typed::Position,
    ) -> SpannedEncodingResult<vir_mid::Position> {
        Ok(position)
    }

    fn typed_to_middle_predicate_expression(
        &self,
        expression: vir_typed::Expression,
    ) -> SpannedEncodingResult<vir_mid::Expression> {
        expression.typed_to_middle_expression(self)
    }

    fn typed_to_middle_predicate_lifetime_const(
        &self,
        lifetime_const: vir_typed::ty::LifetimeConst,
    ) -> SpannedEncodingResult<vir_mid::ty::LifetimeConst> {
        Ok(vir_mid::ty::LifetimeConst {
            name: lifetime_const.name,
        })
    }

    fn typed_to_middle_predicate_trigger(
        &self,
        trigger: vir_typed::Trigger,
    ) -> Result<vir_mid::Trigger, Self::Error> {
        trigger.typed_to_middle_expression(self)
    }

    fn typed_to_middle_predicate_variable_decl(
        &self,
        variable: vir_typed::VariableDecl,
    ) -> Result<vir_mid::VariableDecl, Self::Error> {
        variable.typed_to_middle_expression(self)
    }
}
