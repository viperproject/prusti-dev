use rustc_hash::FxHashSet;
use vir_crate::{
    common::graphviz::ToGraphviz,
    low::{
        self as vir_low,
        ast::statement::visitors::{StatementFolder, StatementWalker},
        expression::visitors::ExpressionWalker,
    },
};

/// The transformations performed:
///
/// 1. Remove all unused labels.
pub(in super::super) fn clean_labels(
    source_filename: &str,
    mut program: vir_low::Program,
) -> vir_low::Program {
    for procedure in std::mem::take(&mut program.procedures) {
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_before_clean_labels",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| procedure.to_graphviz(writer).unwrap(),
            );
        }
        let new_procedure = clean_labels_in_procedure(procedure);
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_after_clean_labels",
                format!("{}.{}.dot", source_filename, new_procedure.name),
                |writer| new_procedure.to_graphviz(writer).unwrap(),
            );
        }
        program.procedures.push(new_procedure);
    }
    program
}

fn clean_labels_in_procedure(mut procedure: vir_low::ProcedureDecl) -> vir_low::ProcedureDecl {
    let mut collector = UsedLabelCollector {
        used_labels: Default::default(),
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
    for block in procedure.basic_blocks.values_mut() {
        for statement in std::mem::take(&mut block.statements) {
            match statement {
                vir_low::Statement::Label(vir_low::LabelStatement { label, .. })
                    if !collector.used_labels.contains(&label) =>
                {
                    // This label is removed.
                }
                _ => block.statements.push(statement),
            }
        }
    }
    procedure
        .custom_labels
        .retain(|label| collector.used_labels.contains(&label.name));
    procedure
}

struct UsedLabelCollector {
    used_labels: FxHashSet<String>,
}

impl StatementWalker for UsedLabelCollector {
    fn walk_expression(&mut self, expression: &vir_low::Expression) {
        ExpressionWalker::walk_expression(self, expression);
    }
}

impl ExpressionWalker for UsedLabelCollector {
    fn walk_labelled_old_enum(&mut self, labelled_old: &vir_low::LabelledOld) {
        if let Some(label) = &labelled_old.label {
            self.used_labels.insert(label.clone());
        }
        self.walk_labelled_old(labelled_old);
    }
    fn walk_trigger(&mut self, trigger: &vir_low::Trigger) {
        for expression in &trigger.terms {
            ExpressionWalker::walk_expression(self, expression);
        }
    }
}
