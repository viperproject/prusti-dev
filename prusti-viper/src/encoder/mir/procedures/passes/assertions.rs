use crate::encoder::{errors::SpannedEncodingResult, Encoder};
use rustc_hash::FxHashMap;
use vir_crate::{
    common::{cfg::Cfg, expression::SyntacticEvaluation},
    high::{self as vir_high},
};

/// Propagate `assert false` backward until it becomes some more specific
/// assertion.
pub(in super::super) fn propagate_assertions_back<'v, 'tcx: 'v>(
    _encoder: &mut Encoder<'v, 'tcx>,
    mut procedure: vir_high::ProcedureDecl,
) -> SpannedEncodingResult<vir_high::ProcedureDecl> {
    // Find all basic blocks containing `assert false` and if `assert false` can
    // be propagated to the beginning of the basic block mark them as
    // unreachable.
    let mut unreachable_blocks = FxHashMap::default();
    for (bb, mut statement_index, statement) in procedure.iter_statements() {
        if let vir_high::Statement::Assert(assert) = statement {
            if assert.expression.is_false() {
                let block = &procedure.basic_blocks[bb];
                let mut can_be_soundly_skipped = true;
                while statement_index > 0 && can_be_soundly_skipped {
                    statement_index -= 1;
                    can_be_soundly_skipped = match &block.statements[statement_index] {
                        vir_high::Statement::Comment(_)
                        | vir_high::Statement::OldLabel(_)
                        | vir_high::Statement::InhalePredicate(vir_high::InhalePredicate {
                            predicate:
                                vir_high::Predicate::LifetimeToken(_)
                                | vir_high::Predicate::MemoryBlockStack(_)
                                | vir_high::Predicate::MemoryBlockStackDrop(_)
                                | vir_high::Predicate::MemoryBlockHeap(_)
                                | vir_high::Predicate::MemoryBlockHeapDrop(_),
                            position: _,
                        })
                        | vir_high::Statement::ExhalePredicate(_)
                        | vir_high::Statement::ExhaleExpression(_)
                        | vir_high::Statement::Consume(_)
                        | vir_high::Statement::Havoc(_)
                        | vir_high::Statement::GhostHavoc(_)
                        | vir_high::Statement::HeapHavoc(_)
                        | vir_high::Statement::Assert(_)
                        | vir_high::Statement::MovePlace(_)
                        | vir_high::Statement::CopyPlace(_)
                        | vir_high::Statement::WritePlace(_)
                        | vir_high::Statement::WriteAddress(_)
                        | vir_high::Statement::Assign(_)
                        | vir_high::Statement::GhostAssign(_)
                        | vir_high::Statement::LeakAll(_)
                        | vir_high::Statement::SetUnionVariant(_)
                        | vir_high::Statement::NewLft(_)
                        | vir_high::Statement::EndLft(_)
                        | vir_high::Statement::DeadReference(_)
                        | vir_high::Statement::DeadReferenceRange(_)
                        | vir_high::Statement::DeadLifetime(_)
                        | vir_high::Statement::DeadInclusion(_)
                        | vir_high::Statement::LifetimeTake(_)
                        | vir_high::Statement::LifetimeReturn(_)
                        | vir_high::Statement::ObtainMutRef(_)
                        | vir_high::Statement::OpenMutRef(_)
                        | vir_high::Statement::OpenFracRef(_)
                        | vir_high::Statement::CloseMutRef(_)
                        | vir_high::Statement::CloseFracRef(_)
                        | vir_high::Statement::BorShorten(_) => true,
                        vir_high::Statement::Pack(_)
                        | vir_high::Statement::Unpack(_)
                        | vir_high::Statement::Obtain(_)
                        | vir_high::Statement::Join(_)
                        | vir_high::Statement::JoinRange(_)
                        | vir_high::Statement::Split(_)
                        | vir_high::Statement::SplitRange(_)
                        | vir_high::Statement::ForgetInitialization(_)
                        | vir_high::Statement::ForgetInitializationRange(_)
                        | vir_high::Statement::RestoreRawBorrowed(_)
                        | vir_high::Statement::Assume(_)
                        | vir_high::Statement::InhalePredicate(_)
                        | vir_high::Statement::InhaleExpression(_)
                        | vir_high::Statement::StashRange(_)
                        | vir_high::Statement::StashRangeRestore(_)
                        | vir_high::Statement::MaterializePredicate(_) => false,
                        vir_high::Statement::LoopInvariant(_) => unreachable!(),
                    };
                }
                if statement_index == 0 {
                    assert!(unreachable_blocks
                        .insert(bb.clone(), assert.position)
                        .is_none());
                }
            }
        }
    }

    // Add assert before successor if we know for sure that we need to go to a
    // specific block.
    for basic_block in procedure.basic_blocks.values_mut() {
        match &basic_block.successor {
            vir_high::Successor::Exit
            | vir_high::Successor::Goto(_)
            | vir_high::Successor::NonDetChoice(_, _) => {}
            vir_high::Successor::GotoSwitch(targets) => {
                if targets.len() == 2 {
                    if let Some(&position) = unreachable_blocks.get(&targets[0].1) {
                        let expression = targets[1].0.clone();
                        basic_block.statements.push(vir_high::Statement::assert(
                            expression.replace_position(position),
                            position,
                        ));
                    } else if let Some(&position) = unreachable_blocks.get(&targets[1].1) {
                        let expression = targets[0].0.clone();
                        basic_block.statements.push(vir_high::Statement::assert(
                            expression.replace_position(position),
                            position,
                        ));
                    }
                }
            }
        }
    }

    Ok(procedure)
}
