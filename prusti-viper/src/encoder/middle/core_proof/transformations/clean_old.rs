use vir_crate::{
    common::graphviz::ToGraphviz,
    low::{
        self as vir_low, ast::statement::visitors::StatementFolder,
        expression::visitors::ExpressionFolder,
    },
};

/// The transformations performed:
///
/// 1. Remove all redundant nested old expressions like
///    `old[label1](old[label1](...))`.
/// 2. Remove all unnecessary old expressions that wrap heap independent
///    expressions.
pub(in super::super) fn clean_old(
    source_filename: &str,
    mut program: vir_low::Program,
) -> vir_low::Program {
    for procedure in std::mem::take(&mut program.procedures) {
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_before_clean_old",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| procedure.to_graphviz(writer).unwrap(),
            );
        }
        let new_procedure = clean_old_in_procedure(procedure);
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_after_clean_old",
                format!("{}.{}.dot", source_filename, new_procedure.name),
                |writer| new_procedure.to_graphviz(writer).unwrap(),
            );
        }
        program.procedures.push(new_procedure);
    }
    program
}

fn clean_old_in_procedure(mut procedure: vir_low::ProcedureDecl) -> vir_low::ProcedureDecl {
    let mut folder = CleanOldFolder {
        current_label: None,
    };
    for block in procedure.basic_blocks.values_mut() {
        for statement in std::mem::take(&mut block.statements) {
            let new_statement = StatementFolder::fold_statement(&mut folder, statement);
            block.statements.push(new_statement);
        }
    }
    procedure
}

struct CleanOldFolder {
    current_label: Option<String>,
}

impl StatementFolder for CleanOldFolder {
    fn fold_expression(&mut self, expression: vir_low::Expression) -> vir_low::Expression {
        ExpressionFolder::fold_expression(self, expression)
    }
}

impl ExpressionFolder for CleanOldFolder {
    fn fold_trigger(&mut self, mut trigger: vir_low::Trigger) -> vir_low::Trigger {
        for term in std::mem::take(&mut trigger.terms) {
            let new_term = ExpressionFolder::fold_expression(self, term);
            trigger.terms.push(new_term);
        }
        trigger
    }

    fn fold_labelled_old_enum(
        &mut self,
        labelled_old: vir_low::LabelledOld,
    ) -> vir_low::Expression {
        if labelled_old.base.is_heap_independent() {
            return ExpressionFolder::fold_expression(self, *labelled_old.base);
        }
        let label = labelled_old.label.as_ref().expect("all labelled old expressions should have a label since we do not use regular preconditions");
        if let Some(current_label) = &self.current_label {
            if label == current_label {
                return ExpressionFolder::fold_expression(self, *labelled_old.base);
            }
        }
        let old_label = self.current_label.take();
        self.current_label = labelled_old.label;
        let expression = ExpressionFolder::fold_expression(self, *labelled_old.base);
        let result = vir_low::Expression::labelled_old(
            self.current_label.take(),
            expression,
            labelled_old.position,
        );
        self.current_label = old_label;
        result
    }
}
