use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use vir_crate::{
    high as vir_high,
    middle::{
        self as vir_mid,
        operations::{
            ToMiddleExpression, ToMiddlePredicate, ToMiddleRvalue, ToMiddleStatementLowerer,
        },
    },
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

    fn to_middle_statement_rvalue(
        &self,
        rvalue: vir_high::Rvalue,
    ) -> SpannedEncodingResult<vir_mid::Rvalue> {
        rvalue.to_middle_rvalue(self)
    }

    fn to_middle_statement_statement_leak_all(
        &self,
        _statement: vir_high::LeakAll,
    ) -> SpannedEncodingResult<vir_mid::Statement> {
        unreachable!("leak-all statement cannot be lowered")
    }

    fn to_middle_statement_statement_set_union_variant(
        &self,
        _statement: vir_high::SetUnionVariant,
    ) -> Result<vir_mid::Statement, Self::Error> {
        unreachable!("set union variant statement cannot be lowered")
    }

    fn to_middle_statement_operand(
        &self,
        operand: vir_high::Operand,
    ) -> Result<vir_mid::Operand, Self::Error> {
        operand.to_middle_rvalue(self)
    }

    fn to_middle_statement_variable_decl(
        &self,
        variable_decl: vir_high::VariableDecl,
    ) -> Result<vir_mid::VariableDecl, <Self as ToMiddleStatementLowerer>::Error> {
        variable_decl.to_middle_expression(self)
    }

    fn to_middle_statement_lifetime_const(
        &self,
        lifetime_const: vir_high::ty::LifetimeConst,
    ) -> Result<vir_mid::ty::LifetimeConst, <Self as ToMiddleStatementLowerer>::Error> {
        Ok(vir_mid::ty::LifetimeConst {
            name: lifetime_const.name,
        })
    }

    fn to_middle_statement_statement_loop_invariant(
        &self,
        _: vir_high::LoopInvariant,
    ) -> Result<vir_mid::Statement, Self::Error> {
        unreachable!("loop invariant statement cannot be lowered")
    }

    fn to_middle_statement_assert(
        &self,
        statement: vir_high::Assert,
    ) -> Result<vir_mid::statement::Assert, Self::Error> {
        Ok(vir_mid::statement::Assert {
            expression: statement.expression.to_middle_expression(self)?,
            condition: None,
            position: statement.position,
        })
    }

    fn to_middle_statement_statement_dead_lifetime(
        &self,
        _statement: vir_high::DeadLifetime,
    ) -> Result<vir_mid::Statement, Self::Error> {
        unreachable!("DeadLifetime statement cannot be lowered");
    }

    fn to_middle_statement_dead_lifetime(
        &self,
        _statement: vir_high::DeadLifetime,
    ) -> Result<vir_mid::statement::DeadLifetime, Self::Error> {
        unreachable!("DeadLifetime statement cannot be lowered");
    }
}
