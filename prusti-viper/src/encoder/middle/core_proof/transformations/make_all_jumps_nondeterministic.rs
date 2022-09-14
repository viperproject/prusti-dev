use vir_crate::{
    common::{
        cfg::Cfg,
        expression::{BinaryOperationHelpers, ExpressionIterator, UnaryOperationHelpers},
        graphviz::ToGraphviz,
    },
    low::{self as vir_low},
};

/// Move jump condition to from the guard to the assumption statement at the
/// beginning of the block.
pub(in super::super) fn make_all_jumps_nondeterministic(
    source_filename: &str,
    mut program: vir_low::Program,
) -> vir_low::Program {
    for procedure in std::mem::take(&mut program.procedures) {
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_before_make_all_jumps_nondeterministic",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| procedure.to_graphviz(writer).unwrap(),
            );
        }
        let new_procedure = make_all_jumps_nondeterministic_in_procedure(procedure);
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_after_make_all_jumps_nondeterministic",
                format!("{}.{}.dot", source_filename, new_procedure.name),
                |writer| new_procedure.to_graphviz(writer).unwrap(),
            );
        }
        program.procedures.push(new_procedure);
    }
    program
}

fn make_all_jumps_nondeterministic_in_procedure(
    mut procedure: vir_low::ProcedureDecl,
) -> vir_low::ProcedureDecl {
    let predecessors = procedure.predecessors_owned();
    let mut counter = 0;
    let mut non_deterministic_choice_counter = 0;
    let mut intermediate_blocks = Vec::new();
    let mut insert_at_start = Vec::new();
    for (source, block) in &mut procedure.basic_blocks {
        match &mut block.successor {
            vir_low::Successor::Return | vir_low::Successor::Goto(_) => {}
            vir_low::Successor::GotoSwitch(expressions) => {
                let mut negated_conditions = Vec::new();
                let variable = vir_low::VariableDecl::new(
                    format!("non_det_branch_choice${}", non_deterministic_choice_counter),
                    vir_low::Type::Int,
                );
                non_deterministic_choice_counter += 1;
                for (i, (condition, target)) in expressions.iter_mut().enumerate() {
                    let condition = std::mem::replace(
                        condition,
                        vir_low::Expression::equals(variable.clone().into(), i.into()),
                    );
                    let assume_condition = vir_low::Statement::assume(
                        vir_low::Expression::and(
                            negated_conditions.clone().into_iter().conjoin(),
                            condition.clone(),
                        ),
                        procedure.position,
                    );
                    if predecessors[target].len() > 1 {
                        let intermediate_label = vir_low::Label::new(format!(
                            "{}__{}__{}",
                            source.name, target.name, counter
                        ));
                        counter += 1;
                        let target = std::mem::replace(target, intermediate_label.clone());
                        let intermediate_block = vir_low::BasicBlock {
                            statements: vec![assume_condition],
                            successor: vir_low::Successor::Goto(target),
                        };
                        intermediate_blocks.push((intermediate_label, intermediate_block));
                    } else {
                        insert_at_start.push((target.clone(), assume_condition));
                    }
                    negated_conditions.push(UnaryOperationHelpers::not(condition));
                }
            }
        }
    }
    procedure.basic_blocks.extend(intermediate_blocks);
    for (target, assume_condition) in insert_at_start {
        procedure
            .basic_blocks
            .get_mut(&target)
            .unwrap()
            .statements
            .insert(0, assume_condition);
    }
    procedure
}
