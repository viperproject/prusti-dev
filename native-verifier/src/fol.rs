use std::collections::HashMap;
use vir::low::{
    ast::{expression::*, statement::*},
    *,
};

pub enum FolStatement {
    Comment(String),
    Assume(Expression),
    Assert(Expression),
}

fn vir_statement_to_fol_statements(
    statement: &Statement,
    known_methods: &HashMap<String, MethodDecl>,
) -> Vec<FolStatement> {
    match statement {
        Statement::Assert(expr) => vec![FolStatement::Assert(expr.expression.clone())],
        Statement::Assume(expr) => vec![FolStatement::Assume(expr.expression.clone())],
        Statement::Inhale(expr) => vec![FolStatement::Assume(expr.expression.clone())],
        Statement::Exhale(expr) => vec![FolStatement::Assert(expr.expression.clone())],
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
            // handle trivial cases where the guard is constant true or false, emit the branches instead
            if let Expression::Constant(Constant {
                value: ConstantValue::Bool(true),
                ..
            }) = cond.guard
            {
                return cond
                    .then_branch
                    .iter()
                    .flat_map(|s| vir_statement_to_fol_statements(s, known_methods))
                    .collect();
            } else if let Expression::Constant(Constant {
                value: ConstantValue::Bool(false),
                ..
            }) = cond.guard
            {
                return cond
                    .else_branch
                    .iter()
                    .flat_map(|s| vir_statement_to_fol_statements(s, known_methods))
                    .collect();
            }

            if !(cond.then_branch.is_empty() && cond.else_branch.is_empty()) {
                unimplemented!(
                    "Non-trivial conditional statements not supported!!\nGuard: {}\n\nThen-branch:\n{}\n\nElse-branch:\n{}",
                    cond.guard,
                    cond.then_branch
                        .iter()
                        .map(|s| format!("{}", s))
                        .collect::<Vec<_>>()
                        .join(";\n"),
                    cond.else_branch
                        .iter()
                        .map(|s| format!("{}", s))
                        .collect::<Vec<_>>()
                        .join(";\n")
                );
            }
            vec![]
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
                        op_kind: op.op_kind.clone(), // TODO: Copy trait derivation
                        argument: Box::new(substitute(&op.argument, mapping)),
                        position: op.position,
                    }),
                    Expression::ContainerOp(op) => Expression::ContainerOp(ContainerOp {
                        kind: op.kind.clone(), // TODO: Copy trait derivation
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
                FolStatement::Assert(substitute(pre, &params_to_args))
            });

            let postconds = method_decl.posts.iter().map(|post| {
                // substitute parameters for arguments
                FolStatement::Assume(substitute(post, &params_to_args))
            });

            preconds.chain(postconds).collect::<Vec<_>>()
        }
        Statement::Comment(comment) => vec![FolStatement::Comment(comment.comment.clone())],
        Statement::LogEvent(_) => vec![], // TODO: Embed in SMT-LIB code
        _ => {
            unimplemented!("Statement {:?} not yet supported", statement);
        }
    }
}

pub fn vir_to_fol(
    statements: &Vec<Statement>,
    known_methods: &HashMap<String, MethodDecl>,
) -> Vec<FolStatement> {
    // reduce so that the order in the vector is now the Sequence operator
    statements
        .iter()
        .flat_map(|s| vir_statement_to_fol_statements(s, known_methods))
        .collect()
}
