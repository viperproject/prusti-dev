use super::{utils::calculate_hash, ProcedureExecutor};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::encoder_context::EncoderContext,
};
use prusti_common::config;
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low},
};

impl<'a, 'c: 'a, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn execute_statement(
        &mut self,
        _current_block: &vir_low::Label,
        statement: &vir_low::Statement,
    ) -> SpannedEncodingResult<()> {
        self.execution_trace_builder
            .add_original_statement(statement.clone())?;
        match statement {
            vir_low::Statement::Comment(statement) => {
                self.execute_statement_comment(statement)?;
            }
            vir_low::Statement::Label(statement) => {
                self.execute_statement_label(statement)?;
            }
            vir_low::Statement::LogEvent(statement) => {
                self.execute_statement_log_event(statement)?;
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
            vir_low::Statement::Fold(_) => unreachable!("{statement}"),
            vir_low::Statement::Unfold(_) => unreachable!("{statement}"),
            vir_low::Statement::ApplyMagicWand(magic_wand) => {
                unreachable!("magic_wand: {magic_wand}");
            }
            vir_low::Statement::MethodCall(method_call) => {
                unreachable!("method_call: {method_call}");
            }
            vir_low::Statement::Assign(statement) => {
                self.execute_statement_assign(statement)?;
            }
            vir_low::Statement::Conditional(_) => {
                unreachable!();
            }
            vir_low::Statement::MaterializePredicate(_) => todo!(),
        }
        Ok(())
    }

    fn execute_statement_comment(
        &mut self,
        statement: &vir_low::ast::statement::Comment,
    ) -> SpannedEncodingResult<()> {
        self.execution_trace_builder
            .heap_comment(statement.clone())?;
        Ok(())
    }

    fn execute_statement_label(
        &mut self,
        statement: &vir_low::ast::statement::Label,
    ) -> SpannedEncodingResult<()> {
        self.execution_trace_builder.heap_label(statement.clone())?;
        Ok(())
    }

    fn execute_statement_log_event(
        &mut self,
        statement: &vir_low::ast::statement::LogEvent,
    ) -> SpannedEncodingResult<()> {
        self.execution_trace_builder
            .current_egraph_state()
            .try_assume_heap_independent_conjuncts(&statement.expression)?;
        self.execution_trace_builder
            .heap_assume(statement.expression.clone(), statement.position)?;
        Ok(())
    }

    fn execute_statement_assume(
        &mut self,
        statement: &vir_low::ast::statement::Assume,
    ) -> SpannedEncodingResult<()> {
        let expression = self.simplify_expression(&statement.expression)?;
        // let expression = statement.expression.clone();
        // self.execution_trace_builder.current_egraph_state().intern_heap_independent_subexpressions(&expression)?;
        self.execution_trace_builder
            .current_egraph_state()
            .try_assume_heap_independent_conjuncts(&expression)?;
        self.execution_trace_builder
            .heap_assume(expression, statement.position)?;
        Ok(())
    }

    fn execute_statement_assert(
        &mut self,
        statement: &vir_low::ast::statement::Assert,
    ) -> SpannedEncodingResult<()> {
        let expression = self.simplify_expression(&statement.expression)?;
        // let expression = statement.expression.clone();
        // self.execution_trace_builder.current_egraph_state().intern_heap_independent_subexpressions(&expression)?;
        self.execution_trace_builder
            .heap_assert(expression, statement.position)?;
        // TODO: Try this:
        // self.execution_trace_builder
        //     .current_egraph_state()
        //     .assume_heap_independent_conjuncts(&statement.expression)?;
        Ok(())
    }

    fn execute_statement_inhale(
        &mut self,
        statement: &vir_low::ast::statement::Inhale,
    ) -> SpannedEncodingResult<()> {
        // We cannot do `let expression =
        // self.simplify_expression(&statement.expression)?;` here because we
        // need to take into account the predicates contained in this expression
        // when simplifying it. Therefore, we simplify each conjunct separately.

        // let expression = self.simplify_expression(&statement.expression)?;
        // self.execution_trace_builder.current_egraph_state().intern_heap_independent_subexpressions(&statement.expression)?;
        self.execute_inhale(&statement.expression, statement.position)?;
        // self.execute_inhale(&expression, statement.position)?;
        Ok(())
    }

    fn execute_inhale(
        &mut self,
        expression: &vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        if let vir_low::Expression::BinaryOp(expression) = expression {
            if expression.op_kind == vir_low::BinaryOpKind::And {
                self.execute_inhale(&expression.left, position)?;
                self.execute_inhale(&expression.right, position)?;
                return Ok(());
            }
        }
        if let vir_low::Expression::PredicateAccessPredicate(predicate) = expression {
            let mut arguments = Vec::new();
            for argument in &predicate.arguments {
                arguments.push(self.simplify_expression(argument)?);
            }
            self.execution_trace_builder.heap_inhale_predicate(
                vir_low::PredicateAccessPredicate::new(
                    predicate.name.clone(),
                    arguments,
                    (*predicate.permission).clone(),
                ),
                self.program_context,
                position,
            )?;
            return Ok(());
        }
        let expression = self.simplify_expression(expression)?;
        // self.execution_trace_builder
        //     .current_egraph_state()
        //     .intern_heap_independent_subexpressions(&expression)?;
        self.execution_trace_builder
            .current_egraph_state()
            .try_assume_heap_independent_conjuncts(&expression)?;
        self.execution_trace_builder
            .heap_inhale_generic(expression, position)?;
        Ok(())
    }

    // fn is_predicate_instance_non_aliased(
    //     &mut self,
    //     predicate: &vir_low::PredicateAccessPredicate,
    // ) -> SpannedEncodingResult<bool> {
    //     if self
    //         .program_context
    //         .is_predicate_kind_non_aliased(&predicate.name)
    //     {
    //         return Ok(true);
    //     }
    //     fn construct_predicate_address_non_aliased_call(
    //         predicate_address: &vir_low::Expression,
    //     ) -> vir_low::Expression {
    //         use vir_low::macros::*;
    //         let address_is_non_aliased = ty!(Bool);
    //         expr! {
    //             (ComputeAddress::address_is_non_aliased([predicate_address.clone()]))
    //         }
    //     }
    //     match self.program_context.get_predicate_kind(&predicate.name) {
    //         vir_low::PredicateKind::MemoryBlock => {
    //             let solver = self.execution_trace_builder.current_egraph_state();
    //             let predicate_address = &predicate.arguments[0];
    //             let predicate_address_non_aliased_call =
    //                 construct_predicate_address_non_aliased_call(predicate_address);
    //             solver.intern_term(&predicate_address_non_aliased_call)?;
    //             solver.saturate()?;
    //             if solver.is_true(&predicate_address_non_aliased_call)? {
    //                 return Ok(true);
    //             }
    //         }
    //         vir_low::PredicateKind::Owned => {
    //             let solver = self.execution_trace_builder.current_egraph_state();
    //             let predicate_address = &predicate.arguments[1];
    //             debug_assert_eq!(predicate_address.get_type(), &vir_low::macros::ty!(Address));
    //             let predicate_address_non_aliased_call =
    //                 construct_predicate_address_non_aliased_call(predicate_address);
    //             solver.intern_term(&predicate_address_non_aliased_call)?;
    //             solver.saturate()?;
    //             if solver.is_true(&predicate_address_non_aliased_call)? {
    //                 return Ok(true);
    //             }
    //         }
    //         _ => {}
    //     }
    //     Ok(false)
    // }

    fn execute_statement_exhale(
        &mut self,
        statement: &vir_low::ast::statement::Exhale,
    ) -> SpannedEncodingResult<()> {
        // let expression = statement.expression.clone();
        let exhale_label = format!(
            "exhale_label$round{}${}",
            self.executor.purification_round, self.exhale_label_generator_counter
        );
        self.exhale_label_generator_counter += 1;
        self.execution_trace_builder
            .heap_label(vir_low::ast::statement::Label {
                label: exhale_label.clone(),
                position: statement.position,
            })?;
        self.execution_trace_builder
            .register_label(vir_low::Label::new(&exhale_label))?;
        self.execute_exhale(&statement.expression, statement.position, &exhale_label)?;
        Ok(())
    }

    fn execute_exhale(
        &mut self,
        expression: &vir_low::Expression,
        position: vir_low::Position,
        exhale_label: &str,
    ) -> SpannedEncodingResult<()> {
        if let vir_low::Expression::BinaryOp(expression) = expression {
            if expression.op_kind == vir_low::BinaryOpKind::And {
                self.execute_exhale(&expression.left, position, exhale_label)?;
                self.execute_exhale(&expression.right, position, exhale_label)?;
                return Ok(());
            }
        }
        if let vir_low::Expression::PredicateAccessPredicate(predicate) = expression {
            let mut arguments = Vec::new();
            for argument in &predicate.arguments {
                let simplified_argument = self.simplify_expression(argument)?;
                arguments.push(simplified_argument.wrap_in_old(exhale_label));
            }
            self.execution_trace_builder.heap_exhale_predicate(
                vir_low::PredicateAccessPredicate::new(
                    predicate.name.clone(),
                    arguments,
                    (*predicate.permission).clone(),
                ),
                self.program_context,
                position,
            )?;
            return Ok(());
        }
        // self.execution_trace_builder.current_egraph_state().intern_heap_independent_subexpressions(&expression)?;
        let expression = self.simplify_expression(expression)?;
        let expression = expression.wrap_in_old(exhale_label);
        self.execution_trace_builder
            .current_egraph_state()
            .try_intern_heap_independent_conjuncts(&expression)?;
        // self.execution_trace_builder
        //     .current_egraph_state()
        //     .saturate()?;
        if expression.is_heap_independent()
            && self
                .execution_trace_builder
                .current_egraph_state()
                .try_is_true(&expression)?
                == Some(true)
        {
            if config::report_symbolic_execution_purification() {
                self.execution_trace_builder
                    .heap_comment(vir_low::Comment::new(format!("purified out: {expression}")))?;
            }
        } else {
            if config::report_symbolic_execution_purification() {
                if self
                    .execution_trace_builder
                    .current_egraph_state()
                    .try_is_true(&expression)?
                    .is_none()
                {
                    self.execution_trace_builder
                        .heap_comment(vir_low::Comment::new(format!(
                            "not interned: {expression}"
                        )))?;
                } else {
                    self.execution_trace_builder
                        .heap_comment(vir_low::Comment::new(format!(
                            "interned, but false: {expression}"
                        )))?;
                    // let debug_info = self
                    //     .execution_trace_builder
                    //     .current_egraph_state()
                    //     .get_dump_eclass_of(&expression)?;
                    // self.execution_trace_builder
                    //     .heap_comment(vir_low::Comment::new(debug_info))?;
                }
            }
            self.execution_trace_builder
                .heap_exhale_generic(expression, position)?;
        }
        Ok(())
    }

    fn execute_statement_assign(
        &mut self,
        statement: &vir_low::ast::statement::Assign,
    ) -> SpannedEncodingResult<()> {
        assert!(
            !statement.position.is_default(),
            "{statement} has no position"
        );
        assert!(statement.value.is_constant());
        let target_variable = self
            .execution_trace_builder
            .create_new_bool_variable_version(&statement.target.name)?;
        let expression =
            vir_low::Expression::equals(target_variable.into(), statement.value.clone());
        self.execution_trace_builder
            .current_egraph_state()
            .try_assume_heap_independent_conjuncts(&expression)?;
        self.execution_trace_builder
            .heap_assume(expression, statement.position)?;
        Ok(())
    }

    fn simplify_expression(
        &mut self,
        expression: &vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.execution_trace_builder
            .current_egraph_state()
            .intern_heap_independent_subexpressions(expression)?;
        let (heap_state, solver) = self
            .execution_trace_builder
            .current_heap_and_egraph_state_mut();
        let purified_expression = heap_state.purify_expression_with_retry(
            solver,
            self.program_context,
            expression.clone(),
        )?;
        let purified_expression_hash = calculate_hash(&purified_expression);
        // let simplified_expression = purified_expression;
        let simplified_expression = super::simplifier::simplify_expression(
            purified_expression,
            self.program_context,
            solver,
        )?;
        if calculate_hash(&simplified_expression) != purified_expression_hash {
            self.execution_trace_builder
                .current_egraph_state()
                .intern_heap_independent_subexpressions(&simplified_expression)?;
        }
        Ok(simplified_expression)
    }
}
