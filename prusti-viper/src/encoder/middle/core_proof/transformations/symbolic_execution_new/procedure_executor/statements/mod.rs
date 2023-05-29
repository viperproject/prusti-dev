use super::{super::super::encoder_context::EncoderContext, ProcedureExecutor};
use crate::encoder::errors::SpannedEncodingResult;

use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low},
};

mod inhale;
mod exhale;

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn add_statement(
        &mut self,
        statement: vir_low::Statement,
    ) -> SpannedEncodingResult<()> {
        let builder = self.current_builder_mut();
        builder.add_statement(statement)
    }

    pub(super) fn add_statements(
        &mut self,
        statements: Vec<vir_low::Statement>,
    ) -> SpannedEncodingResult<()> {
        let builder = self.current_builder_mut();
        builder.add_statements(statements)
    }

    pub(super) fn add_comment(&mut self, comment: String) -> SpannedEncodingResult<()> {
        self.add_statement(vir_low::Statement::comment(comment))
    }

    pub(super) fn add_assume(
        &mut self,
        expression: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        self.add_statement(vir_low::Statement::assume(expression, position))
    }

    pub(super) fn execute_statement(
        &mut self,
        statement: &vir_low::Statement,
    ) -> SpannedEncodingResult<()> {
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
            vir_low::Statement::Comment(_) | vir_low::Statement::LogEvent(_) => {
                self.add_statement(statement.clone())?;
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
        }
        Ok(())
    }

    fn execute_statement_label(
        &mut self,
        statement: &vir_low::ast::statement::Label,
    ) -> SpannedEncodingResult<()> {
        self.save_state(statement.label.clone())?;
        self.add_statement(vir_low::Statement::Label(statement.clone()))?;
        Ok(())
    }

    fn execute_statement_assign(
        &mut self,
        statement: &vir_low::ast::statement::Assign,
    ) -> SpannedEncodingResult<()> {
        assert!(statement.value.is_constant());
        let target_variable = self.create_new_bool_variable_version(&statement.target.name)?;
        let expression =
            vir_low::Expression::equals(target_variable.into(), statement.value.clone());
        self.try_assume_heap_independent_conjuncts(&expression)?;
        self.add_assume(expression, statement.position)?;
        Ok(())
    }

    fn execute_statement_assume(
        &mut self,
        statement: &vir_low::ast::statement::Assume,
    ) -> SpannedEncodingResult<()> {
        let expression = self.simplify_expression(&statement.expression, statement.position)?;
        self.try_assume_heap_independent_conjuncts(&expression)?;
        self.add_statement(vir_low::Statement::assume(expression, statement.position))?;
        Ok(())
    }

    fn execute_statement_assert(
        &mut self,
        statement: &vir_low::ast::statement::Assert,
    ) -> SpannedEncodingResult<()> {
        let expression = self.simplify_expression(&statement.expression, statement.position)?;
        self.try_assume_heap_independent_conjuncts(&expression)?;
        self.add_statement(vir_low::Statement::assert(expression, statement.position))?;
        Ok(())
    }

    fn execute_statement_inhale(
        &mut self,
        statement: &vir_low::ast::statement::Inhale,
    ) -> SpannedEncodingResult<()> {
        self.execute_inhale(&statement.expression, statement.position)?;
        self.current_builder_mut().set_materialization_point()?;
        Ok(())
    }

    fn execute_statement_exhale(
        &mut self,
        statement: &vir_low::ast::statement::Exhale,
    ) -> SpannedEncodingResult<()> {
        let exhale_label = format!("exhale_label${}", self.exhale_label_generator_counter);
        self.exhale_label_generator_counter += 1;
        self.register_label(vir_low::Label::new(exhale_label.clone()))?;
        let label = vir_low::ast::statement::Label::new(exhale_label.clone());
        self.execute_statement_label(&label)?;
        self.execute_exhale(&statement.expression, statement.position, &exhale_label)?;
        // self.current_builder_mut().set_materialization_point()?;
        Ok(())
    }

    fn execute_materialize_predicate(
        &mut self,
        statement: &vir_low::ast::statement::MaterializePredicate,
    ) -> SpannedEncodingResult<()> {
        let vir_low::Expression::PredicateAccessPredicate(predicate) = self.simplify_expression(&statement.predicate, statement.position)? else {
            unreachable!();
        };
        self.materialize_predicate(predicate, statement.check_that_exists, statement.position)?;
        Ok(())
    }
}
