use rustc_hash::FxHashSet;
use vir_crate::{
    common::graphviz::ToGraphviz,
    low::{
        self as vir_low, ast::statement::visitors::StatementWalker,
        expression::visitors::ExpressionWalker,
    },
};

/// The transformations performed:
///
/// 1. Remove unused variables.
pub(in super::super) fn clean_variables(
    source_filename: &str,
    mut program: vir_low::Program,
) -> vir_low::Program {
    for procedure in std::mem::take(&mut program.procedures) {
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_before_clean_variables",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| procedure.to_graphviz(writer).unwrap(),
            );
        }
        let new_procedure = clean_variables_in_procedure(procedure);
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_after_clean_variables",
                format!("{}.{}.dot", source_filename, new_procedure.name),
                |writer| new_procedure.to_graphviz(writer).unwrap(),
            );
        }
        program.procedures.push(new_procedure);
    }
    program
}

fn clean_variables_in_procedure(mut procedure: vir_low::ProcedureDecl) -> vir_low::ProcedureDecl {
    let mut collector = UsedVariableCollector {
        used_variables: Default::default(),
    };
    for block in procedure.basic_blocks.values() {
        for statement in &block.statements {
            collector.walk_statement(statement);
        }
        match &block.successor {
            vir_low::Successor::Return | vir_low::Successor::Goto(_) => {}
            vir_low::Successor::GotoSwitch(expressions) => {
                for (expression, _) in expressions {
                    ExpressionWalker::walk_expression(&mut collector, expression);
                }
            }
        }
    }
    procedure
        .locals
        .retain(|local| collector.used_variables.contains(&local.name));
    procedure
}

struct UsedVariableCollector {
    used_variables: FxHashSet<String>,
}

impl StatementWalker for UsedVariableCollector {
    fn walk_expression(&mut self, expression: &vir_low::Expression) {
        ExpressionWalker::walk_expression(self, expression);
    }
    fn walk_variable_decl(&mut self, variable_decl: &vir_low::VariableDecl) {
        self.used_variables.insert(variable_decl.name.clone());
    }
}

impl ExpressionWalker for UsedVariableCollector {
    fn walk_variable_decl(&mut self, variable_decl: &vir_low::VariableDecl) {
        self.used_variables.insert(variable_decl.name.clone());
    }
    fn walk_trigger(&mut self, trigger: &vir_low::Trigger) {
        for expression in &trigger.terms {
            ExpressionWalker::walk_expression(self, expression);
        }
    }
}
