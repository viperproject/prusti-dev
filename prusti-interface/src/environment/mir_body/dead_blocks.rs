use prusti_rustc_interface::{
    index::{bit_set::BitSet, Idx},
    middle::mir,
};
use std::collections::BTreeMap;

// Adapted from
// https://github.com/rust-lang/rust/blob/aedf78e56b2279cc869962feac5153b6ba7001ed/compiler/rustc_mir_transform/src/simplify.rs#L263-L295
// Main changes: remove session, return the replacements.
pub fn remove_dead_blocks<'tcx>(
    body: &mut mir::Body<'tcx>,
    reachable: &BitSet<mir::BasicBlock>,
) -> BTreeMap<mir::BasicBlock, mir::BasicBlock> {
    let num_blocks = body.basic_blocks.len();

    let basic_blocks = body.basic_blocks_mut();
    let mut replacements: Vec<_> = (0..num_blocks).map(mir::BasicBlock::new).collect();
    let mut inverse_replacements = BTreeMap::default();
    let mut used_blocks = 0;
    for alive_index in reachable.iter() {
        let alive_index = alive_index.index();
        replacements[alive_index] = mir::BasicBlock::new(used_blocks);
        inverse_replacements.insert(
            mir::BasicBlock::new(used_blocks),
            mir::BasicBlock::new(alive_index),
        );
        if alive_index != used_blocks {
            // Swap the next alive block data with the current available slot. Since
            // alive_index is non-decreasing this is a valid operation.
            basic_blocks.raw.swap(alive_index, used_blocks);
        }
        used_blocks += 1;
    }

    basic_blocks.raw.truncate(used_blocks);

    for block in basic_blocks {
        for target in block.terminator_mut().successors_mut() {
            *target = replacements[target.index()];
        }
    }

    inverse_replacements
}
