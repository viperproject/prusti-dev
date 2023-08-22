use rustc_hash::FxHashMap;
use vir_crate::{
    common::expression::{ExpressionIterator, UnaryOperationHelpers},
    low::{self as vir_low},
};
use vir_low::expression::visitors::ExpressionFolder;

pub(crate) fn inline_caller_for(program: &mut vir_low::Program) {
    let caller_for_functions = program
        .functions
        .extract_if(|function| function.kind == vir_low::FunctionKind::CallerFor)
        .map(|function| (function.name.clone(), function))
        .collect();
    for procedure in &mut program.procedures {
        for block in &mut procedure.basic_blocks {
            inline_in_statements(&mut block.statements, &caller_for_functions);
        }
    }
}

fn inline_in_statements(
    statements: &mut Vec<vir_low::Statement>,
    caller_for_functions: &FxHashMap<String, vir_low::FunctionDecl>,
) {
    let old_statements = std::mem::take(statements);
    let mut inliner = Inliner {
        caller_for_functions,
        statements,
        path_condition: Vec::new(),
    };
    let mut sentinel = true.into();
    for statement in old_statements {
        assert!(inliner.path_condition.is_empty());
        match statement {
            vir_low::Statement::Assume(mut statement) => {
                sentinel =
                    inliner.fold_expression(std::mem::replace(&mut statement.expression, sentinel));
                std::mem::swap(&mut statement.expression, &mut sentinel);
                inliner
                    .statements
                    .push(vir_low::Statement::Assume(statement));
            }
            vir_low::Statement::Assert(mut statement) => {
                sentinel =
                    inliner.fold_expression(std::mem::replace(&mut statement.expression, sentinel));
                std::mem::swap(&mut statement.expression, &mut sentinel);
                inliner
                    .statements
                    .push(vir_low::Statement::Assert(statement));
            }
            vir_low::Statement::Comment(_)
            | vir_low::Statement::LogEvent(_)
            | vir_low::Statement::Inhale(_)
            | vir_low::Statement::Exhale(_)
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
    statements: &'a mut Vec<vir_low::Statement>,
    path_condition: Vec<vir_low::Expression>,
}

impl<'a> ExpressionFolder for Inliner<'a> {
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
            function
                .body
                .clone()
                .unwrap()
                .substitute_variables(&replacements)
        } else {
            vir_low::Expression::FuncApp(self.fold_func_app(func_app))
        }
    }
}
