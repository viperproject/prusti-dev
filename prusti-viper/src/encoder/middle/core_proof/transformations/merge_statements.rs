use rustc_hash::FxHashSet;
use vir_crate::{
    common::{expression::ExpressionIterator, graphviz::ToGraphviz},
    low::{
        self as vir_low,
        ast::statement::visitors::{StatementFolder, StatementWalker},
        expression::visitors::ExpressionWalker,
    },
};

/// The transformations performed:
///
/// 1. Remove all unused labels.
pub(in super::super) fn merge_statements(
    source_filename: &str,
    mut program: vir_low::Program,
) -> vir_low::Program {
    for procedure in std::mem::take(&mut program.procedures) {
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_before_merge_statements",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| procedure.to_graphviz(writer).unwrap(),
            );
        }
        let new_procedure = merge_statements_in_procedure(procedure);
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_after_merge_statements",
                format!("{}.{}.dot", source_filename, new_procedure.name),
                |writer| new_procedure.to_graphviz(writer).unwrap(),
            );
        }
        program.procedures.push(new_procedure);
    }
    program
}

fn merge_statements_in_procedure(mut procedure: vir_low::ProcedureDecl) -> vir_low::ProcedureDecl {
    for block in procedure.basic_blocks.values_mut() {
        let statements = std::mem::take(&mut block.statements);
        merge_statements_in_block(&mut block.statements, statements);
    }
    procedure
}

#[derive(PartialEq, Eq, Hash)]
enum ExpressionKind {
    None,
    Inhale,
    Exhale,
    Assume,
    Assert,
}

fn merge_statements_in_block(
    new_statements: &mut Vec<vir_low::Statement>,
    statements: Vec<vir_low::Statement>,
) {
    let mut conjuncts = Vec::new();
    let mut expression_kind = ExpressionKind::None;
    let mut last_position = vir_low::Position::default();
    for statement in statements {
        match statement {
            vir_low::Statement::Comment(_) => {}
            vir_low::Statement::Assume(statement) => {
                if expression_kind != ExpressionKind::Assume
                    && expression_kind != ExpressionKind::None
                {
                    new_statements.push(create_statement(
                        expression_kind,
                        &mut conjuncts,
                        last_position,
                    ));
                }
                expression_kind = ExpressionKind::Assume;
                conjuncts.push(statement.expression);
                last_position = statement.position;
            }
            vir_low::Statement::Assert(statement) => {
                if expression_kind != ExpressionKind::Assert
                    && expression_kind != ExpressionKind::None
                {
                    new_statements.push(create_statement(
                        expression_kind,
                        &mut conjuncts,
                        last_position,
                    ));
                }
                expression_kind = ExpressionKind::Assert;
                conjuncts.push(statement.expression);
                last_position = statement.position;
            }
            vir_low::Statement::Inhale(statement) => {
                if expression_kind != ExpressionKind::Inhale
                    && expression_kind != ExpressionKind::None
                {
                    new_statements.push(create_statement(
                        expression_kind,
                        &mut conjuncts,
                        last_position,
                    ));
                }
                expression_kind = ExpressionKind::Inhale;
                conjuncts.push(statement.expression);
                last_position = statement.position;
            }
            vir_low::Statement::Exhale(statement) => {
                if expression_kind != ExpressionKind::Exhale
                    && expression_kind != ExpressionKind::None
                {
                    new_statements.push(create_statement(
                        expression_kind,
                        &mut conjuncts,
                        last_position,
                    ));
                }
                expression_kind = ExpressionKind::Exhale;
                conjuncts.push(statement.expression);
                last_position = statement.position;
            }
            _ => {
                new_statements.push(statement);
            }
        }
    }
    if !conjuncts.is_empty() {
        new_statements.push(create_statement(
            expression_kind,
            &mut conjuncts,
            last_position,
        ));
    }
}

fn create_statement(
    expression_kind: ExpressionKind,
    conjuncts: &mut Vec<vir_low::Expression>,
    position: vir_low::Position,
) -> vir_low::Statement {
    let expression = std::mem::take(conjuncts).into_iter().conjoin();
    match expression_kind {
        ExpressionKind::Assume => vir_low::Statement::assume(expression, position),
        ExpressionKind::Assert => vir_low::Statement::assert(expression, position),
        ExpressionKind::Inhale => vir_low::Statement::inhale(expression, position),
        ExpressionKind::Exhale => vir_low::Statement::exhale(expression, position),
        ExpressionKind::None => unreachable!(),
    }
}
