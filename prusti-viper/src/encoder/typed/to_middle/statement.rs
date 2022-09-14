use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use vir_crate::{
    middle::{
        self as vir_mid,
        operations::{
            TypedToMiddleExpression, TypedToMiddlePredicate, TypedToMiddleRvalue,
            TypedToMiddleStatementLowerer,
        },
    },
    typed as vir_typed,
};

impl<'v, 'tcx> TypedToMiddleStatementLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn typed_to_middle_statement_position(
        &self,
        position: vir_typed::Position,
    ) -> SpannedEncodingResult<vir_mid::Position> {
        assert!(!position.is_default());
        Ok(position)
    }

    fn typed_to_middle_statement_expression(
        &self,
        expression: vir_typed::Expression,
    ) -> SpannedEncodingResult<vir_mid::Expression> {
        expression.typed_to_middle_expression(self)
    }

    fn typed_to_middle_statement_predicate(
        &self,
        predicate: vir_typed::Predicate,
    ) -> SpannedEncodingResult<vir_mid::Predicate> {
        predicate.typed_to_middle_predicate(self)
    }

    fn typed_to_middle_statement_rvalue(
        &self,
        rvalue: vir_typed::Rvalue,
    ) -> SpannedEncodingResult<vir_mid::Rvalue> {
        rvalue.typed_to_middle_rvalue(self)
    }

    fn typed_to_middle_statement_statement_leak_all(
        &self,
        _statement: vir_typed::LeakAll,
    ) -> SpannedEncodingResult<vir_mid::Statement> {
        unreachable!("leak-all statement cannot be lowered")
    }

    fn typed_to_middle_statement_operand(
        &self,
        operand: vir_typed::Operand,
    ) -> Result<vir_mid::Operand, Self::Error> {
        operand.typed_to_middle_rvalue(self)
    }

    fn typed_to_middle_statement_variable_decl(
        &self,
        variable_decl: vir_typed::VariableDecl,
    ) -> Result<vir_mid::VariableDecl, Self::Error> {
        variable_decl.typed_to_middle_expression(self)
    }

    fn typed_to_middle_statement_lifetime_const(
        &self,
        lifetime_const: vir_typed::ty::LifetimeConst,
    ) -> Result<vir_mid::ty::LifetimeConst, Self::Error> {
        Ok(vir_mid::ty::LifetimeConst {
            name: lifetime_const.name,
        })
    }

    fn typed_to_middle_statement_statement_loop_invariant(
        &self,
        _: vir_typed::LoopInvariant,
    ) -> Result<vir_mid::Statement, Self::Error> {
        unreachable!("loop invariant statement cannot be lowered")
    }

    fn typed_to_middle_statement_assert(
        &self,
        statement: vir_typed::Assert,
    ) -> Result<vir_mid::statement::Assert, Self::Error> {
        Ok(vir_mid::statement::Assert {
            expression: statement.expression.typed_to_middle_expression(self)?,
            condition: None,
            position: statement.position,
        })
    }

    fn typed_to_middle_statement_statement_dead_lifetime(
        &self,
        _statement: vir_typed::DeadLifetime,
    ) -> Result<vir_mid::Statement, Self::Error> {
        unreachable!("DeadLifetime statement cannot be lowered");
    }

    fn typed_to_middle_statement_dead_lifetime(
        &self,
        _statement: vir_typed::DeadLifetime,
    ) -> Result<vir_mid::statement::DeadLifetime, Self::Error> {
        unreachable!("DeadLifetime statement cannot be lowered");
    }

    fn typed_to_middle_statement_statement_obtain_mut_ref(
        &self,
        _statement: vir_typed::ObtainMutRef,
    ) -> Result<vir_mid::statement::Statement, Self::Error> {
        unreachable!("ObtainMutRef statement cannot be lowered");
    }

    fn typed_to_middle_statement_statement_unpack(
        &self,
        _statement: vir_typed::Unpack,
    ) -> Result<vir_mid::Statement, Self::Error> {
        unreachable!("Unpack statement cannot be lowered");
    }

    fn typed_to_middle_statement_statement_pack(
        &self,
        _statement: vir_typed::Pack,
    ) -> Result<vir_mid::Statement, Self::Error> {
        unreachable!("Pack statement cannot be lowered");
    }

    fn typed_to_middle_statement_statement_forget_initialization(
        &self,
        _statement: vir_typed::ForgetInitialization,
    ) -> Result<vir_mid::Statement, Self::Error> {
        unreachable!("ForgetInitialization statement cannot be lowered");
    }

    fn typed_to_middle_statement_statement_split(
        &self,
        _statement: vir_typed::Split,
    ) -> Result<vir_mid::Statement, Self::Error> {
        unreachable!("Split statement cannot be lowered");
    }

    fn typed_to_middle_statement_statement_join(
        &self,
        _statement: vir_typed::Join,
    ) -> Result<vir_mid::Statement, Self::Error> {
        unreachable!("Join statement cannot be lowered");
    }

    // fn typed_to_middle_statement_statement_restore(
    //             &self,
    //             _statement: vir_typed::Restore,
    //         ) -> Result<vir_mid::Statement, Self::Error> {
    //     unreachable!("Restore statement cannot be lowered");
    // }
}
