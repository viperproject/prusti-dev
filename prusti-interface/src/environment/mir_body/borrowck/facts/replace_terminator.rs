use prusti_rustc_interface::middle::mir;

#[derive(Debug, Clone)]
pub struct ReplaceTerminatorDesugaring {
    /// The location of the `Drop` terminator that replaces the `DropAndReplace`
    /// terminator.
    pub replacing_drop_location: mir::Location,
    /// The location of the target block of the new `Drop` terminator.
    pub target_block: mir::BasicBlock,
    /// The location of the unwinding block of the new `Drop` terminator.
    pub unwinding_block: mir::BasicBlock,
}

pub fn collect_replace_terminators<'tcx>(
    old_body: &mir::Body<'tcx>,
    new_body: &mir::Body<'tcx>,
) -> Vec<ReplaceTerminatorDesugaring> {
    let mut replace_terminator_locations = Vec::new();
    for (_, old_block) in old_body.basic_blocks.iter_enumerated() {
        if let mir::TerminatorKind::DropAndReplace { .. } = old_block.terminator().kind {
            unreachable!("DropAndReplace should be removed by now");
            // let new_block = &new_body.basic_blocks[index];
            // if let mir::TerminatorKind::Drop { target, unwind, .. } = new_block.terminator().kind {
            //     let unwinding_block = unwind.expect("unimplemented: DropAndReplace without unwind");
            //     let desugaring = ReplaceTerminatorDesugaring {
            //         replacing_drop_location: mir::Location {
            //             block: index,
            //             statement_index: new_block.statements.len(),
            //         },
            //         target_block: target,
            //         unwinding_block,
            //     };
            //     replace_terminator_locations.push(desugaring);
            //     let target_block_data = &new_body.basic_blocks[target];
            //     let unwind_block_data = &new_body.basic_blocks[unwinding_block];
            //     // Assert the properties on which we rely in
            //     // prusti-interface/src/environment/mir_body/borrowck/lifetimes/mod.rs.
            //     assert_eq!(unwind_block_data.statements.len(), 1);
            //     assert_eq!(target_block_data.statements.len(), 1);
            // } else {
            //     unimplemented!("DropAndReplace should be replaced by Drop");
            // }
        }
    }
    for (index, new_block) in new_body.basic_blocks.iter_enumerated() {
        if let mir::TerminatorKind::Drop {
            place,
            target,
            unwind: Some(unwind),
        } = new_block.terminator().kind
        {
            let target_block_data = &new_body.basic_blocks[target];
            let unwind_block_data = &new_body.basic_blocks[unwind];
            if target_block_data.statements.len() == 1 && unwind_block_data.statements.len() == 1 {
                if let mir::StatementKind::Assign(box (target_place, _)) =
                    target_block_data.statements[0].kind
                {
                    if let mir::StatementKind::Assign(box (unwind_place, _)) =
                        unwind_block_data.statements[0].kind
                    {
                        // FIXME: Check whether I can use
                        // `DesugaringKind::Replace` to reliably detect this
                        // case instead. https://github.com/rust-lang/rust/pull/107844
                        if place == target_place && place == unwind_place {
                            // This is likely a desugaring of a `DropAndReplace` terminator.
                            let desugaring = ReplaceTerminatorDesugaring {
                                replacing_drop_location: mir::Location {
                                    block: index,
                                    statement_index: new_block.statements.len(),
                                },
                                target_block: target,
                                unwinding_block: unwind,
                            };
                            replace_terminator_locations.push(desugaring);
                        }
                    }
                }
            }
        }
    }
    replace_terminator_locations
}
