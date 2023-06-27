use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use vir_crate::{
    high as vir_high,
    typed::{
        self as vir_typed,
        operations::{
            HighToTypedExpression, HighToTypedPredicate, HighToTypedRvalue,
            HighToTypedStatementLowerer,
        },
    },
};

impl<'v, 'tcx> HighToTypedStatementLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn high_to_typed_statement_position(
        &mut self,
        position: vir_high::Position,
    ) -> SpannedEncodingResult<vir_typed::Position> {
        assert!(!position.is_default());
        Ok(position)
    }

    fn high_to_typed_statement_expression(
        &mut self,
        expression: vir_high::Expression,
    ) -> SpannedEncodingResult<vir_typed::Expression> {
        expression.high_to_typed_expression(self)
    }

    fn high_to_typed_statement_lifetime_const(
        &mut self,
        lifetime_const: vir_high::ty::LifetimeConst,
    ) -> Result<vir_typed::ty::LifetimeConst, Self::Error> {
        Ok(vir_typed::ty::LifetimeConst {
            name: lifetime_const.name,
        })
    }

    fn high_to_typed_statement_variable_decl(
        &mut self,
        variable_decl: vir_high::VariableDecl,
    ) -> Result<vir_typed::VariableDecl, Self::Error> {
        variable_decl.high_to_typed_expression(self)
    }

    fn high_to_typed_statement_rvalue(
        &mut self,
        rvalue: vir_high::Rvalue,
    ) -> SpannedEncodingResult<vir_typed::Rvalue> {
        rvalue.high_to_typed_rvalue(self)
    }

    fn high_to_typed_statement_predicate(
        &mut self,
        predicate: vir_high::Predicate,
    ) -> SpannedEncodingResult<vir_typed::Predicate> {
        predicate.high_to_typed_predicate(self)
    }

    fn high_to_typed_statement_basic_block_id(
        &mut self,
        label: vir_high::BasicBlockId,
    ) -> Result<vir_typed::BasicBlockId, Self::Error> {
        Ok(vir_typed::BasicBlockId { name: label.name })
    }

    fn high_to_typed_statement_operand(
        &mut self,
        operand: vir_high::Operand,
    ) -> Result<vir_typed::Operand, Self::Error> {
        operand.high_to_typed_rvalue(self)
    }

    fn high_to_typed_statement_uniqueness(
        &mut self,
        uniqueness: vir_high::ty::Uniqueness,
    ) -> Result<vir_typed::ty::Uniqueness, Self::Error> {
        Ok(match uniqueness {
            vir_high::ty::Uniqueness::Shared => vir_typed::ty::Uniqueness::Shared,
            vir_high::ty::Uniqueness::Unique => vir_typed::ty::Uniqueness::Unique,
        })
    }
}
