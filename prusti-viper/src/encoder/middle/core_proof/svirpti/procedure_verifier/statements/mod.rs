use super::{
    super::{
        super::transformations::{
            encoder_context::EncoderContext, symbolic_execution_new::ProgramContext,
        },
        smt::{SmtSolver, Sort2SmtWrap},
        VerificationResult, Verifier,
    },
    ProcedureExecutor,
};
use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low},
};

mod exhale;
mod inhale;

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn execute_statement(
        &mut self,
        statement: &vir_low::Statement,
    ) -> SpannedEncodingResult<()> {
        eprintln!("Executing statement: {}", statement);
        match statement {
            vir_low::Statement::Label(statement) => {
                self.execute_statement_label(statement)?;
            }
            vir_low::Statement::Assign(statement) => {
                self.execute_statement_assign(statement)?;
            }
            vir_low::Statement::Assume(statement) => {
                self.execute_statement_assume(statement)?;
            }
            vir_low::Statement::Assert(statement) => {
                self.execute_statement_assert(statement)?;
            }
            vir_low::Statement::Inhale(statement) => {
                self.execute_statement_inhale(statement)?;
            }
            vir_low::Statement::Exhale(statement) => {
                self.execute_statement_exhale(statement)?;
            }
            vir_low::Statement::Comment(statement) => {
                self.smt_solver.comment(&statement.to_string()).unwrap(); // TODO: handle error
            }
            vir_low::Statement::LogEvent(statement) => {
                self.smt_solver.comment(&statement.to_string()).unwrap(); // TODO: handle error
            }
            vir_low::Statement::Fold(_)
            | vir_low::Statement::Unfold(_)
            | vir_low::Statement::ApplyMagicWand(_)
            | vir_low::Statement::MethodCall(_)
            | vir_low::Statement::Conditional(_) => {
                unreachable!();
            }
            vir_low::Statement::MaterializePredicate(statement) => {
                self.execute_materialize_predicate(statement)?;
            }
            vir_low::Statement::CaseSplit(statement) => {
                self.execute_case_split(statement)?;
            }
        }
        Ok(())
    }

    fn execute_statement_label(
        &mut self,
        statement: &vir_low::ast::statement::Label,
    ) -> SpannedEncodingResult<()> {
        unimplemented!();
        // self.save_state(statement.label.clone())?;
        // self.add_statement(vir_low::Statement::Label(statement.clone()))?;
        Ok(())
    }

    fn execute_statement_assign(
        &mut self,
        statement: &vir_low::ast::statement::Assign,
    ) -> SpannedEncodingResult<()> {
        assert!(statement.value.is_constant());
        unimplemented!();
        // let target_variable = self.create_new_bool_variable_version(&statement.target.name)?;
        // let expression =
        //     vir_low::Expression::equals(target_variable.into(), statement.value.clone());
        // self.try_assume_heap_independent_conjuncts(&expression)?;
        // self.add_assume(expression, statement.position)?;
        Ok(())
    }

    fn execute_statement_assume(
        &mut self,
        statement: &vir_low::ast::statement::Assume,
    ) -> SpannedEncodingResult<()> {
        self.assume(&statement.expression)?;
        Ok(())
    }

    fn execute_statement_assert(
        &mut self,
        statement: &vir_low::ast::statement::Assert,
    ) -> SpannedEncodingResult<()> {
        unimplemented!();
        // let expression = self.simplify_expression(&statement.expression, statement.position)?;
        // self.try_assume_heap_independent_conjuncts(&expression)?;
        // self.add_statement(vir_low::Statement::assert(expression, statement.position))?;
        Ok(())
    }

    fn execute_statement_inhale(
        &mut self,
        statement: &vir_low::ast::statement::Inhale,
    ) -> SpannedEncodingResult<()> {
        self.execute_inhale(&statement.expression, statement.position)?;
        Ok(())
    }

    fn execute_statement_exhale(
        &mut self,
        statement: &vir_low::ast::statement::Exhale,
    ) -> SpannedEncodingResult<()> {
        unimplemented!("statement: {statement}");
        // let exhale_label = format!("exhale_label${}", self.exhale_label_generator_counter);
        // self.exhale_label_generator_counter += 1;
        // self.register_label(vir_low::Label::new(exhale_label.clone()))?;
        // let label = vir_low::ast::statement::Label::new(exhale_label.clone());
        // self.execute_statement_label(&label)?;
        // self.execute_exhale(&statement.expression, statement.position, &exhale_label)?;
        Ok(())
    }

    fn execute_materialize_predicate(
        &mut self,
        statement: &vir_low::ast::statement::MaterializePredicate,
    ) -> SpannedEncodingResult<()> {
        unimplemented!();
        // let vir_low::Expression::PredicateAccessPredicate(predicate) = self.simplify_expression(&statement.predicate, statement.position)? else {
        //     unreachable!();
        // };
        // self.materialize_predicate(predicate, statement.check_that_exists, statement.position)?;
        Ok(())
    }

    fn execute_case_split(
        &mut self,
        statement: &vir_low::ast::statement::CaseSplit,
    ) -> SpannedEncodingResult<()> {
        unimplemented!();
        // let expression = self.simplify_expression(&statement.expression, statement.position)?;
        // self.add_statement(vir_low::Statement::case_split(
        //     expression,
        //     statement.position,
        // ))?;
        Ok(())
    }
}
