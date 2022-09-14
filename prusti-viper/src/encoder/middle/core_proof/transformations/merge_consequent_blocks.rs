use vir_crate::{
    common::{cfg::Cfg, graphviz::ToGraphviz},
    low::{self as vir_low},
};

/// Merges consequent basic blocks into one.
pub(in super::super) fn merge_consequent_blocks(
    source_filename: &str,
    mut program: vir_low::Program,
) -> vir_low::Program {
    for procedure in std::mem::take(&mut program.procedures) {
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_before_merge_consequent_blocks",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| procedure.to_graphviz(writer).unwrap(),
            );
        }
        let new_procedure = merge_consequent_blocks_in_procedure(procedure);
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_after_merge_consequent_blocks",
                format!("{}.{}.dot", source_filename, new_procedure.name),
                |writer| new_procedure.to_graphviz(writer).unwrap(),
            );
        }
        program.procedures.push(new_procedure);
    }
    program
}

fn merge_consequent_blocks_in_procedure(
    mut procedure: vir_low::ProcedureDecl,
) -> vir_low::ProcedureDecl {
    let traversal_order = procedure.get_topological_sort();
    let predecessors = procedure.predecessors_owned();
    for label in traversal_order {
        if let Some(mut block) = procedure.basic_blocks.get(&label) {
            while let vir_low::Successor::Goto(target) = &block.successor {
                if predecessors[target].len() == 1 {
                    let target = target.clone();
                    let mut target_block = procedure.basic_blocks.remove(&target).unwrap();
                    let mut source_block = procedure.basic_blocks.get_mut(&label).unwrap();
                    source_block
                        .statements
                        .push(vir_low::Statement::comment(format!(
                            "Merged in block: {}",
                            target
                        )));
                    source_block
                        .statements
                        .push(vir_low::Statement::label_no_pos(target.name.clone()));
                    source_block.statements.append(&mut target_block.statements);
                    source_block.successor = target_block.successor;
                    if let Some(next_block) = procedure.basic_blocks.get(&label) {
                        block = next_block;
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
    }

    // let mut edges_to_remove = Vec::new();
    // for (source, block) in &procedure.basic_blocks {
    //     match &block.successor {
    //         vir_low::Successor::Goto(target) => {
    //             if predecessors[target].len() == 1 {
    //                 edges_to_remove.push((source.clone(), target.clone()));
    //             }
    //         }
    //         vir_low::Successor::Return | vir_low::Successor::GotoSwitch(_) => {}
    //     }
    // }
    // let mut groups: Vec<usize> = (0..edges_to_remove.len()).into_iter().collect();
    // for (i, (source1, target1)) in edges_to_remove.iter().enumerate() {
    //     for (j, (source2, target2)) in edges_to_remove[i + 1..].iter().enumerate() {
    //         assert!(!(source1 == source2 && target1 == target2));
    //         if target1 == source2 {
    //             let j = j + i + 1;
    //             groups[j] = groups[i];
    //         }
    //     }
    // }
    // for i in 0..edges_to_remove.len() {
    //     let (source, target) = &edges_to_remove[i];
    //     let (main_source, _) = &edges_to_remove[groups[i]];
    //     // Merge target block into main_source block.
    //     let main_source_block = procedure.basic_blocks.get_mut(main_source).unwrap();

    // }
    procedure
}
