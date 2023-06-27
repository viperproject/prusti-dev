use vir_crate::{
    common::graphviz::ToGraphviz,
    low::{self as vir_low, operations::ty::Typed},
};

pub(crate) fn desugar_implications(
    source_filename: &str,
    mut program: vir_low::Program,
) -> vir_low::Program {
    let mut procedures = Vec::new();
    for procedure in std::mem::take(&mut program.procedures) {
        let procedure = desugar_implications_in_procedure(procedure);
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_after_desugar_implications",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| procedure.to_graphviz(writer).unwrap(),
            );
        }
        procedures.push(procedure);
    }
    program.procedures = procedures;
    program
}

fn desugar_implications_in_procedure(
    mut procedure: vir_low::ProcedureDecl,
) -> vir_low::ProcedureDecl {
    let mut label_counter: u64 = 0;
    for block in procedure.basic_blocks.values_mut() {
        desugar_statements(
            std::mem::take(&mut block.statements),
            &mut block.statements,
            &mut procedure.custom_labels,
            &mut label_counter,
        );
    }
    procedure
}

fn desugar_statements(
    old_statements: Vec<vir_low::Statement>,
    new_statements: &mut Vec<vir_low::Statement>,
    custom_labels: &mut Vec<vir_low::Label>,
    label_counter: &mut u64,
) {
    for statement in old_statements {
        match statement {
            vir_low::Statement::Assume(statement) => {
                desugar_expression(
                    new_statements,
                    statement.expression,
                    statement.position,
                    &mut vir_low::Statement::assume,
                );
            }
            vir_low::Statement::Assert(statement) => {
                desugar_expression(
                    new_statements,
                    statement.expression,
                    statement.position,
                    &mut vir_low::Statement::assert,
                );
            }
            vir_low::Statement::Inhale(statement) => {
                desugar_expression(
                    new_statements,
                    statement.expression,
                    statement.position,
                    &mut vir_low::Statement::inhale,
                );
            }
            vir_low::Statement::Exhale(statement) => {
                let label = format!("desugar_impls_label${label_counter}");
                *label_counter += 1;
                let expression = statement.expression.wrap_in_old(&label);
                new_statements.push(vir_low::Statement::label(label.clone(), statement.position));
                custom_labels.push(vir_low::Label::new(label));
                desugar_expression(
                    new_statements,
                    expression,
                    statement.position,
                    &mut vir_low::Statement::exhale,
                );
            }
            vir_low::Statement::Conditional(mut statement) => {
                desugar_statements(
                    std::mem::take(&mut statement.then_branch),
                    &mut statement.then_branch,
                    custom_labels,
                    label_counter,
                );
                desugar_statements(
                    std::mem::take(&mut statement.else_branch),
                    &mut statement.else_branch,
                    custom_labels,
                    label_counter,
                );
                new_statements.push(vir_low::Statement::Conditional(statement));
            }
            _ => {
                new_statements.push(statement);
            }
        }
    }
}

fn desugar_expression(
    statements: &mut Vec<vir_low::Statement>,
    expression: vir_low::Expression,
    position: vir_low::Position,
    statement_constructor: &mut impl FnMut(vir_low::Expression, vir_low::Position) -> vir_low::Statement,
) {
    match expression {
        // _ if expression.is_pure() => {
        //     statements.push(statement_constructor(expression, position));
        // }
        vir_low::Expression::BinaryOp(binary_op_expression)
            if matches!(
                binary_op_expression.op_kind,
                vir_low::BinaryOpKind::And | vir_low::BinaryOpKind::Implies
            ) =>
        {
            match binary_op_expression.op_kind {
                vir_low::BinaryOpKind::And => {
                    desugar_expression(
                        statements,
                        *binary_op_expression.left,
                        position,
                        statement_constructor,
                    );
                    desugar_expression(
                        statements,
                        *binary_op_expression.right,
                        position,
                        statement_constructor,
                    );
                }
                vir_low::BinaryOpKind::Implies => {
                    let mut then_statements = Vec::new();
                    desugar_expression(
                        &mut then_statements,
                        *binary_op_expression.right,
                        position,
                        statement_constructor,
                    );
                    statements.push(vir_low::Statement::conditional(
                        *binary_op_expression.left,
                        then_statements,
                        Vec::new(),
                        position,
                    ));
                }
                _ => {
                    unreachable!();
                }
            }
        }
        vir_low::Expression::Conditional(conditional_expression) => {
            assert_eq!(conditional_expression.get_type(), &vir_low::Type::Bool);
            let mut then_statements = Vec::new();
            desugar_expression(
                &mut then_statements,
                *conditional_expression.then_expr,
                position,
                statement_constructor,
            );
            let mut else_statements = Vec::new();
            desugar_expression(
                &mut else_statements,
                *conditional_expression.else_expr,
                position,
                statement_constructor,
            );
            statements.push(vir_low::Statement::conditional(
                *conditional_expression.guard,
                then_statements,
                else_statements,
                position,
            ));
        }
        _ => {
            statements.push(statement_constructor(expression, position));
        }
    }
}
