use std::collections::HashMap;
use vir::{
    common::position::Positioned,
    low::{
        ast::{expression::*, statement::*},
        expression::visitors::ExpressionFolder,
        *,
    },
};

pub enum FolStatement {
    Comment(String),
    Assume(Expression),
    Assert {
        expression: Expression,
        reason: Option<Position>,
    },
}

pub fn set_position(expr: Expression, new_position: Position) -> Expression {
    struct PositionReplacer {
        new_position: Position,
    }
    impl ExpressionFolder for PositionReplacer {
        fn fold_position(&mut self, _: Position) -> Position {
            self.new_position
        }
    }
    PositionReplacer { new_position }.fold_expression(expr)
}

fn vir_statement_to_fol_statements(
    statement: &Statement,
    known_methods: &HashMap<String, MethodDecl>,
) -> Vec<FolStatement> {
    match statement {
        Statement::Assume(expr) => vec![FolStatement::Assume(expr.expression.clone())],
        Statement::Inhale(expr) => vec![FolStatement::Assume(expr.expression.clone())],
        Statement::Assert(expr) => {
            let reason_pos = expr.expression.position();
            let failure_pos = expr.position;

            if reason_pos != failure_pos {
                vec![FolStatement::Assert {
                    expression: set_position(expr.expression.clone(), failure_pos),
                    reason: Some(reason_pos),
                }]
            } else {
                vec![FolStatement::Assert {
                    expression: expr.expression.clone(),
                    reason: None,
                }]
            }
        }
        Statement::Exhale(expr) => {
            let reason_pos = expr.expression.position();
            let failure_pos = expr.position;

            if reason_pos != failure_pos {
                vec![FolStatement::Assert {
                    expression: set_position(expr.expression.clone(), failure_pos),
                    reason: Some(reason_pos),
                }]
            } else {
                vec![FolStatement::Assert {
                    expression: expr.expression.clone(),
                    reason: None,
                }]
            }
        }
        Statement::Assign(assign) => {
            let eq = Expression::BinaryOp(BinaryOp {
                op_kind: BinaryOpKind::EqCmp,
                left: Box::new(Expression::Local(Local {
                    variable: assign.target.clone(),
                    position: assign.position,
                })),
                right: Box::new(assign.value.clone()),
                position: assign.position,
            });

            vec![FolStatement::Assume(eq)]
        }
        Statement::Conditional(cond) => {
            let negate_guard = Expression::UnaryOp(UnaryOp {
                op_kind: UnaryOpKind::Not,
                argument: Box::new(cond.guard.clone()),
                position: cond.guard.position(),
            });

            let mut statements = vec![];
            for (guard, branch) in [
                (cond.guard.clone(), &cond.then_branch),
                (negate_guard, &cond.else_branch),
            ] {
                for s in branch {
                    if let Statement::Assert(assert) = s {
                        let implication = Expression::BinaryOp(BinaryOp {
                            op_kind: BinaryOpKind::Implies,
                            left: Box::new(guard.clone()),
                            right: Box::new(assert.expression.clone()),
                            position: assert.position,
                        });
                        statements.push(FolStatement::Assert {
                            expression: implication,
                            reason: None, // TODO: Reason?
                        });
                    } else if let Statement::Inhale(inhale) = s {
                        let implication = Expression::BinaryOp(BinaryOp {
                            op_kind: BinaryOpKind::Implies,
                            left: Box::new(guard.clone()),
                            right: Box::new(inhale.expression.clone()),
                            position: inhale.position,
                        });
                        statements.push(FolStatement::Assume(implication));
                    } else {
                        unimplemented!(
                            "Non-assertion statements in conditionals not supported: {}",
                            s
                        )
                    }
                }
            }
            return statements;
        }
        Statement::MethodCall(method_call) => {
            let method_decl = known_methods
                .get(&method_call.method_name)
                .expect("Method not found");

            let mut params_to_args = method_decl
                .parameters
                .iter()
                .zip(method_call.arguments.iter())
                .map(|(target, arg)| (target.clone(), arg.clone()))
                .collect::<HashMap<_, _>>();

            let returns_to_targets = method_decl
                .targets
                .iter()
                .zip(method_call.targets.iter())
                .map(|(target, arg)| (target.clone(), arg.clone()))
                .collect::<HashMap<_, _>>();

            params_to_args.extend(returns_to_targets);

            fn substitute(
                expr: &Expression,
                mapping: &HashMap<VariableDecl, Expression>,
            ) -> Expression {
                match expr {
                    Expression::Local(local) => {
                        if let Some(arg) = mapping.get(&local.variable) {
                            arg.clone()
                        } else {
                            Expression::Local(local.clone())
                        }
                    }
                    Expression::BinaryOp(op) => Expression::BinaryOp(BinaryOp {
                        op_kind: op.op_kind,
                        left: Box::new(substitute(&op.left, mapping)),
                        right: Box::new(substitute(&op.right, mapping)),
                        position: op.position,
                    }),
                    Expression::UnaryOp(op) => Expression::UnaryOp(UnaryOp {
                        op_kind: op.op_kind,
                        argument: Box::new(substitute(&op.argument, mapping)),
                        position: op.position,
                    }),
                    Expression::ContainerOp(op) => Expression::ContainerOp(ContainerOp {
                        kind: op.kind,
                        container_type: op.container_type.clone(),
                        operands: op
                            .operands
                            .iter()
                            .map(|arg| substitute(arg, mapping))
                            .collect(),
                        position: op.position,
                    }),
                    Expression::Constant(constant) => Expression::Constant(constant.clone()),
                    Expression::DomainFuncApp(func) => Expression::DomainFuncApp(DomainFuncApp {
                        domain_name: func.domain_name.clone(),
                        function_name: func.function_name.clone(),
                        arguments: func
                            .arguments
                            .iter()
                            .map(|arg| substitute(arg, mapping))
                            .collect(),
                        parameters: func.parameters.clone(),
                        return_type: func.return_type.clone(),
                        position: func.position,
                    }),
                    Expression::MagicWand(magic_wand) => Expression::MagicWand(MagicWand {
                        left: Box::new(substitute(&magic_wand.left, mapping)),
                        right: Box::new(substitute(&magic_wand.right, mapping)),
                        position: magic_wand.position,
                    }),
                    _ => unimplemented!("substitute not implemented for {:?}", expr),
                }
            }

            let preconds = method_decl.pres.iter().map(|pre| {
                // substitute parameters for arguments
                FolStatement::Assert {
                    expression: substitute(pre, &params_to_args),
                    reason: None,
                }
            });

            let postconds = method_decl.posts.iter().map(|post| {
                // substitute parameters for arguments
                FolStatement::Assume(substitute(post, &params_to_args))
            });

            preconds.chain(postconds).collect::<Vec<_>>()
        }
        Statement::Comment(comment) => vec![FolStatement::Comment(comment.comment.clone())],
        Statement::LogEvent(_) => vec![], // ignored
        _ => {
            unimplemented!("Statement {:?} not yet supported", statement);
        }
    }
}

pub fn vir_to_fol(
    statements: &[Statement],
    known_methods: &HashMap<String, MethodDecl>,
) -> Vec<FolStatement> {
    statements
        .iter()
        .flat_map(|s| vir_statement_to_fol_statements(s, known_methods))
        .collect()
}
