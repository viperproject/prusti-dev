use vir_crate::{
    common::{expression::UnaryOperationHelpers, graphviz::ToGraphviz},
    low::{self as vir_low},
};

pub(crate) fn desugar_conditionals(
    source_filename: &str,
    mut program: vir_low::Program,
) -> vir_low::Program {
    let mut procedures = Vec::new();
    for procedure in std::mem::take(&mut program.procedures) {
        let procedure = desugar_conditionals_in_procedure(procedure);
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_after_desugar_conditionals",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| procedure.to_graphviz(writer).unwrap(),
            );
        }
        procedures.push(procedure);
    }
    program.procedures = procedures;
    program
}

fn new_label(prefix: &str, label_counter: &mut usize) -> vir_low::Label {
    let label = format!("{prefix}__{label_counter}");
    *label_counter += 1;
    vir_low::Label::new(label)
}

fn desugar_conditionals_in_procedure(
    mut procedure: vir_low::ProcedureDecl,
) -> vir_low::ProcedureDecl {
    let mut work_queue: Vec<_> = procedure.basic_blocks.keys().cloned().collect();
    let mut label_counter = 0;
    while let Some(current_label) = work_queue.pop() {
        let block = procedure.basic_blocks.get_mut(&current_label).unwrap();
        if let Some(conditional_position) = block
            .statements
            .iter()
            .position(|statement| matches!(statement, vir_low::Statement::Conditional(_)))
        {
            let remaining_statements = block.statements.split_off(conditional_position + 1);
            let vir_low::Statement::Conditional(conditional) = block.statements.pop().unwrap() else {
                unreachable!();
            };
            let remaining_block_label = new_label("remaining_block_label", &mut label_counter);
            let then_block_label = new_label("then_block_label", &mut label_counter);
            let else_block_label = new_label("else_block_label", &mut label_counter);
            let then_block = vir_low::BasicBlock {
                statements: conditional.then_branch,
                successor: vir_low::Successor::Goto(remaining_block_label.clone()),
            };

            let mut targets = vec![(conditional.guard.clone(), then_block_label.clone())];
            let negated_guard = vir_low::Expression::not(conditional.guard.clone());
            let else_block = if conditional.else_branch.is_empty() {
                targets.push((negated_guard, remaining_block_label.clone()));
                None
            } else {
                let else_block = vir_low::BasicBlock {
                    statements: conditional.else_branch,
                    successor: vir_low::Successor::Goto(remaining_block_label.clone()),
                };
                targets.push((negated_guard, else_block_label.clone()));
                Some(else_block)
            };
            let new_successor = vir_low::Successor::GotoSwitch(targets);
            let original_successor = std::mem::replace(&mut block.successor, new_successor);
            let remaining_block = vir_low::BasicBlock {
                statements: remaining_statements,
                successor: original_successor,
            };
            work_queue.push(remaining_block_label.clone());
            work_queue.push(then_block_label.clone());
            procedure
                .basic_blocks
                .insert(then_block_label.clone(), then_block);
            if let Some(else_block) = else_block {
                work_queue.push(else_block_label.clone());
                procedure
                    .basic_blocks
                    .insert(else_block_label.clone(), else_block);
            }
            procedure
                .basic_blocks
                .insert(remaining_block_label.clone(), remaining_block);
        }
    }
    procedure
}
