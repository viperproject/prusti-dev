use std::collections::BTreeSet;

use rustc_hash::FxHashMap;
use vir_crate::{
    common::{
        expression::{ExpressionIterator, UnaryOperationHelpers},
        graphviz::ToGraphviz,
    },
    low::{self as vir_low},
};
use vir_low::expression::visitors::ExpressionFolder;

use crate::encoder::middle::core_proof::utils::bound_variable_stack::{
    BoundVariableStack, BoundVariableStackLow,
};

pub(crate) fn inline_caller_for(source_filename: &str, program: &mut vir_low::Program) {
    let mut caller_for_functions = program
        .functions
        .drain_filter(|function| function.kind == vir_low::FunctionKind::CallerFor)
        .map(|function| (function.name.clone(), function))
        .collect();
    let mut failed_to_inline_functions = Default::default();
    for procedure in &mut program.procedures {
        let mut inliner = Inliner {
            caller_for_functions: &caller_for_functions,
            statements: Vec::new(),
            path_condition: Vec::new(),
            bound_variable_stack: Default::default(),
            failed_to_inline_functions: &mut failed_to_inline_functions,
        };
        for block in procedure.basic_blocks.values_mut() {
            inline_in_statements(&mut inliner, std::mem::take(&mut block.statements));
            match &mut block.successor {
                vir_low::Successor::Return => {}
                vir_low::Successor::Goto(_) => {}
                vir_low::Successor::GotoSwitch(targets) => {
                    let mut new_targets = Vec::new();
                    for (guard, target) in std::mem::take(targets) {
                        let guard = inliner.fold_expression(guard);
                        new_targets.push((guard, target));
                    }
                    block.successor = vir_low::Successor::GotoSwitch(new_targets);
                }
            }
            block.statements = std::mem::take(&mut inliner.statements);
        }
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_after_inline_caller_for",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| procedure.to_graphviz(writer).unwrap(),
            );
        }
    }
    for function_name in failed_to_inline_functions {
        program
            .functions
            .push(caller_for_functions.remove(&function_name).unwrap());
    }
}

fn inline_in_statements(inliner: &mut Inliner, old_statements: Vec<vir_low::Statement>) {
    for statement in old_statements {
        assert!(inliner.path_condition.is_empty());
        match statement {
            vir_low::Statement::Assume(statement) => {
                inliner.inline_statement(
                    statement.expression,
                    statement.position,
                    vir_low::Statement::assume,
                );
            }
            vir_low::Statement::Assert(statement) => {
                inliner.inline_statement(
                    statement.expression,
                    statement.position,
                    vir_low::Statement::assert,
                );
            }
            vir_low::Statement::Inhale(statement) => {
                inliner.inline_statement(
                    statement.expression,
                    statement.position,
                    vir_low::Statement::inhale,
                );
            }
            vir_low::Statement::Exhale(statement) => {
                inliner.inline_statement(
                    statement.expression,
                    statement.position,
                    vir_low::Statement::exhale,
                );
            }
            vir_low::Statement::Comment(_)
            | vir_low::Statement::Label(_)
            | vir_low::Statement::LogEvent(_)
            | vir_low::Statement::Fold(_)
            | vir_low::Statement::Unfold(_)
            | vir_low::Statement::ApplyMagicWand(_)
            | vir_low::Statement::MethodCall(_)
            | vir_low::Statement::Assign(_)
            | vir_low::Statement::Conditional(_) => {
                inliner.statements.push(statement);
            }
        }
    }
}

struct Inliner<'a> {
    caller_for_functions: &'a FxHashMap<String, vir_low::FunctionDecl>,
    statements: Vec<vir_low::Statement>,
    path_condition: Vec<vir_low::Expression>,
    bound_variable_stack: BoundVariableStack,
    failed_to_inline_functions: &'a mut BTreeSet<String>,
}

impl<'a> Inliner<'a> {
    fn inline_statement(
        &mut self,
        expression: vir_low::Expression,
        position: vir_low::Position,
        constructor: fn(vir_low::Expression, vir_low::Position) -> vir_low::Statement,
    ) {
        let expression = self.fold_expression(expression);
        let statement = constructor(expression, position);
        self.statements.push(statement);
    }
}

impl<'a> ExpressionFolder for Inliner<'a> {
    fn fold_quantifier_enum(&mut self, quantifier: vir_low::Quantifier) -> vir_low::Expression {
        let mut quantifier = quantifier;
        self.bound_variable_stack.push(&quantifier.variables);
        quantifier = self.fold_quantifier(quantifier);
        self.bound_variable_stack.pop();
        quantifier.into()
    }

    fn fold_binary_op(
        &mut self,
        mut binary_op: vir_low::expression::BinaryOp,
    ) -> vir_low::expression::BinaryOp {
        binary_op.left = self.fold_expression_boxed(binary_op.left);
        if binary_op.op_kind == vir_low::BinaryOpKind::Implies {
            self.path_condition.push((*binary_op.left).clone());
        }
        binary_op.right = self.fold_expression_boxed(binary_op.right);
        if binary_op.op_kind == vir_low::BinaryOpKind::Implies {
            self.path_condition.pop();
        }
        binary_op
    }

    fn fold_conditional(
        &mut self,
        mut conditional: vir_low::expression::Conditional,
    ) -> vir_low::expression::Conditional {
        conditional.guard = self.fold_expression_boxed(conditional.guard);
        self.path_condition.push((*conditional.guard).clone());
        conditional.then_expr = self.fold_expression_boxed(conditional.then_expr);
        self.path_condition.pop();
        self.path_condition
            .push(vir_low::Expression::not((*conditional.guard).clone()));
        conditional.else_expr = self.fold_expression_boxed(conditional.else_expr);
        self.path_condition.pop();
        conditional
    }

    fn fold_func_app_enum(
        &mut self,
        func_app: vir_low::expression::FuncApp,
    ) -> vir_low::Expression {
        if let Some(function) = self.caller_for_functions.get(&func_app.function_name) {
            if !self
                .bound_variable_stack
                .expressions_contains_bound_variables(&func_app.arguments)
                && !self
                    .bound_variable_stack
                    .expressions_contains_bound_variables(&self.path_condition)
            {
                let path_condition = self.path_condition.iter().cloned().conjoin();
                assert_eq!(function.parameters.len(), func_app.arguments.len());
                let arguments: Vec<_> = func_app
                    .arguments
                    .into_iter()
                    .map(|argument| self.fold_expression(argument))
                    .collect();
                let replacements = function.parameters.iter().zip(arguments.iter()).collect();
                let pres = function
                    .pres
                    .iter()
                    .cloned()
                    .conjoin()
                    .substitute_variables(&replacements);
                use vir_low::macros::*;
                self.statements.push(stmtp! { func_app.position =>
                    assert ([path_condition] ==> [pres])
                });
                let new_function = function
                    .body
                    .clone()
                    .unwrap()
                    .substitute_variables(&replacements);
                return new_function;
            } else {
                self.failed_to_inline_functions
                    .insert(func_app.function_name.clone());
            }
        }
        vir_low::Expression::FuncApp(self.fold_func_app(func_app))
    }
}
