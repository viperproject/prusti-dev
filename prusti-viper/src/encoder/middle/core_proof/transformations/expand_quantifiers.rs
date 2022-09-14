use vir_crate::{
    common::graphviz::ToGraphviz,
    low::{self as vir_low},
};

pub(crate) fn expand_quantifiers(
    source_filename: &str,
    mut program: vir_low::Program,
) -> vir_low::Program {
    let mut procedures = Vec::new();
    for procedure in std::mem::take(&mut program.procedures) {
        let procedure = expand_quantifiers_in_procedure(procedure);
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_after_expand_quantifiers",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| procedure.to_graphviz(writer).unwrap(),
            );
        }
        procedures.push(procedure);
    }
    program.procedures = procedures;
    program
}

fn expand_quantifiers_in_procedure(
    mut procedure: vir_low::ProcedureDecl,
) -> vir_low::ProcedureDecl {
    let mut counter = 0;
    for block in procedure.basic_blocks.values_mut() {
        for statement in std::mem::take(&mut block.statements) {
            match statement {
                vir_low::Statement::Assert(statement) => {
                    desugar_expression(
                        &mut counter,
                        &mut procedure.locals,
                        &mut block.statements,
                        statement.expression,
                        statement.position,
                        &mut vir_low::Statement::assert,
                    );
                }
                vir_low::Statement::Exhale(statement) if statement.expression.is_pure() => {
                    desugar_expression(
                        &mut counter,
                        &mut procedure.locals,
                        &mut block.statements,
                        statement.expression,
                        statement.position,
                        &mut vir_low::Statement::exhale,
                    );
                }
                _ => {
                    block.statements.push(statement);
                }
            }
        }
    }
    procedure
}

fn desugar_expression(
    variable_counter: &mut usize,
    locals: &mut Vec<vir_low::VariableDecl>,
    statements: &mut Vec<vir_low::Statement>,
    expression: vir_low::Expression,
    position: vir_low::Position,
    statement_constructor: &mut impl FnMut(vir_low::Expression, vir_low::Position) -> vir_low::Statement,
) {
    match expression {
        vir_low::Expression::Quantifier(quantifier)
            if quantifier.kind == vir_low::QuantifierKind::ForAll =>
        {
            statements.push(vir_low::Statement::comment(format!(
                "desugaring forall {quantifier}"
            )));
            let mut variable_expressions = Vec::new();
            for bound_variable in &quantifier.variables {
                let variable = vir_low::VariableDecl::new(
                    format!("{}$quantifier${}", bound_variable.name, variable_counter),
                    bound_variable.ty.clone(),
                );
                *variable_counter += 1;
                statements.push(vir_low::Statement::comment(format!(
                    "  {bound_variable} → {variable}"
                )));
                locals.push(variable.clone());
                variable_expressions.push(variable.clone().into());
            }
            let replacements = quantifier
                .variables
                .iter()
                .zip(variable_expressions.iter())
                .collect();
            let body = quantifier.body.substitute_variables(&replacements);
            let assertion = match body {
                vir_low::Expression::BinaryOp(binary_expression)
                    if binary_expression.op_kind == vir_low::BinaryOpKind::Implies =>
                {
                    statements.push(vir_low::Statement::assume(
                        *binary_expression.left,
                        position,
                    ));
                    *binary_expression.right
                }
                body => body,
            };
            statements.push(vir_low::Statement::assert(assertion, position));
        }
        _ => {
            statements.push(statement_constructor(expression, position));
        }
    }
}
