use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    mir::errors::ErrorInterface,
    Encoder,
};
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    common::cfg::Cfg,
    high::{
        self as vir_high,
        ast::{expression::visitors::ExpressionFolder, statement::visitors::StatementFolder},
    },
};

pub(in super::super) fn desugar_loops<'v, 'tcx: 'v>(
    encoder: &mut Encoder<'v, 'tcx>,
    mut procedure: vir_high::ProcedureDecl,
) -> SpannedEncodingResult<vir_high::ProcedureDecl> {
    let mut is_first = true;
    while let Some((invariant_block_id, loop_invariant)) = find_loop_invariant(&procedure) {
        let loop_head = loop_invariant.loop_head.clone();
        let back_edges = loop_invariant.back_edges.clone();

        if is_first {
            is_first = false;
            let leak = vir_high::BasicBlock {
                statements: vec![vir_high::Statement::leak_all()],
                successor: vir_high::Successor::Goto(procedure.exit.clone()),
            };
            assert!(procedure
                .basic_blocks
                .insert(construct_magic_label(), leak)
                .is_none());
        }

        let duplicated_loop_head =
            duplicate_blocks(encoder, &mut procedure, &invariant_block_id, &loop_head)?;

        for back_edge in &back_edges {
            let block = procedure.basic_blocks.get_mut(back_edge).unwrap();
            block.successor.map_basic_block_ids(|bb| {
                if bb == &loop_head {
                    *bb = duplicated_loop_head.clone()
                }
            });
        }

        let invariant_block = procedure.basic_blocks.get_mut(&invariant_block_id).unwrap();
        let loop_invariant = invariant_block
            .statements
            .pop()
            .unwrap()
            .unwrap_loop_invariant();

        invariant_block
            .statements
            .push(vir_high::Statement::comment(
                "Loop Invariant Functional Specifications".to_string(),
            ));
        for assertion in &loop_invariant.functional_specifications {
            let statement = encoder.set_surrounding_error_context_for_statement(
                vir_high::Statement::assert_no_pos(assertion.clone()),
                loop_invariant.position,
                ErrorCtxt::AssertLoopInvariantOnEntry,
            )?;
            invariant_block.statements.push(statement);
        }

        // Note: It is important for soundness that we havoc here everything
        // that could potentially be mutated in the loop body. This means that
        // we should always fully havoc all aliased memory.

        invariant_block
            .statements
            .push(vir_high::Statement::comment(
                "Loop Invariant Maybe Modified Places".to_string(),
            ));
        for predicate in loop_invariant.maybe_modified_places {
            let statement = encoder.set_surrounding_error_context_for_statement(
                vir_high::Statement::havoc_no_pos(predicate),
                loop_invariant.position,
                ErrorCtxt::UnexpectedAssumeLoopInvariantOnEntry,
            )?;
            invariant_block.statements.push(statement);
        }

        for assertion in loop_invariant.functional_specifications {
            let statement = encoder.set_surrounding_error_context_for_statement(
                vir_high::Statement::assume_no_pos(assertion),
                loop_invariant.position,
                ErrorCtxt::UnexpectedAssumeLoopInvariantOnEntry,
            )?;
            invariant_block.statements.push(statement);
        }
    }
    Ok(procedure)
}

fn find_loop_invariant(
    procedure: &vir_high::ProcedureDecl,
) -> Option<(vir_high::BasicBlockId, &vir_high::LoopInvariant)> {
    for (bb, _, statement) in procedure.iter_statements() {
        if let vir_high::Statement::LoopInvariant(loop_invariant) = statement {
            return Some((bb.clone(), loop_invariant));
        }
    }
    None
}

fn duplicate_blocks<'v, 'tcx: 'v>(
    encoder: &mut Encoder<'v, 'tcx>,
    procedure: &mut vir_high::ProcedureDecl,
    invariant_block: &vir_high::BasicBlockId,
    loop_head: &vir_high::BasicBlockId,
) -> SpannedEncodingResult<vir_high::BasicBlockId> {
    let (blocks_to_duplicate, old_labels_remap) = {
        let predecessors = procedure.predecessors();
        let mut old_labels_remap = BTreeMap::new();
        let mut blocks_to_duplicate = BTreeSet::new();
        let mut work_queue = vec![invariant_block];
        while let Some(block) = work_queue.pop() {
            blocks_to_duplicate.insert(block.clone());
            for statement in &procedure.basic_blocks[block].statements {
                if let vir_high::Statement::OldLabel(label) = statement {
                    assert!(old_labels_remap
                        .insert(
                            label.name.clone(),
                            format!("loop__{}__{}", loop_head, label.name)
                        )
                        .is_none());
                }
            }
            if block != loop_head {
                work_queue.extend(&predecessors[block]);
            }
        }
        (blocks_to_duplicate, old_labels_remap)
    };
    let new_label = |bb: &vir_high::BasicBlockId| {
        if blocks_to_duplicate.contains(bb) {
            vir_high::BasicBlockId::new(format!("loop__{}__{}", loop_head, bb))
        } else {
            bb.clone()
        }
    };
    let mut updater = OldLabelUpdater { old_labels_remap };
    for bb in &blocks_to_duplicate {
        let mut block = procedure.basic_blocks[bb].clone();
        if bb == invariant_block {
            let loop_invariant = block.statements.pop().unwrap().unwrap_loop_invariant();
            for assertion in loop_invariant.functional_specifications {
                let statement = encoder.set_surrounding_error_context_for_statement(
                    vir_high::Statement::assert_no_pos(assertion),
                    loop_invariant.position,
                    ErrorCtxt::AssertLoopInvariantAfterIteration,
                )?;
                block.statements.push(statement);
            }
            let statement = encoder.set_surrounding_error_context_for_statement(
                vir_high::Statement::assume_no_pos(false.into()),
                loop_invariant.position,
                ErrorCtxt::AssertLoopInvariantAfterIteration,
            )?;
            block.statements.push(statement);
            block.successor = vir_high::Successor::Goto(construct_magic_label());
        } else {
            block
                .successor
                .map_basic_block_ids(|bb| *bb = new_label(bb));
        }
        for statement in std::mem::take(&mut block.statements) {
            block.statements.push(updater.fold_statement(statement));
        }
        assert!(procedure
            .basic_blocks
            .insert(new_label(bb), block)
            .is_none())
    }
    Ok(new_label(loop_head))
}

fn construct_magic_label() -> vir_high::BasicBlockId {
    vir_high::BasicBlockId::new("magic_label".to_string())
}

struct OldLabelUpdater {
    old_labels_remap: BTreeMap<String, String>,
}

impl StatementFolder for OldLabelUpdater {
    fn fold_expression(&mut self, expression: vir_high::Expression) -> vir_high::Expression {
        ExpressionFolder::fold_expression(self, expression)
    }
    fn fold_old_label(&mut self, statement: vir_high::OldLabel) -> vir_high::OldLabel {
        if let Some(new_label) = self.old_labels_remap.get(&statement.name) {
            vir_high::OldLabel {
                name: new_label.clone(),
                ..statement
            }
        } else {
            statement
        }
    }
}

impl ExpressionFolder for OldLabelUpdater {
    fn fold_labelled_old(&mut self, expression: vir_high::LabelledOld) -> vir_high::LabelledOld {
        let mut expression = vir_high::visitors::default_fold_labelled_old(self, expression);
        if let Some(new_label) = self.old_labels_remap.get(&expression.label) {
            expression.label = new_label.clone();
        }
        expression
    }
}
