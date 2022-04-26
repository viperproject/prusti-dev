use prusti_interface::environment::is_marked_specification_block;
use rustc_data_structures::graph::WithSuccessors;
use rustc_middle::{mir, ty::TyCtxt};
use std::collections::BTreeSet;

/// Information about the specification blocks.
pub(super) struct SpecificationBlocks {
    /// All blocks that are generated as a result of specification type-checking.
    specification_blocks: BTreeSet<mir::BasicBlock>,
    /// Blocks through which specifications are entered.
    specification_entry_blocks: BTreeSet<mir::BasicBlock>,
}

impl SpecificationBlocks {
    pub(super) fn build<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Self {
        // Blocks that contain closures marked with `#[spec_only]` attributes.
        let mut marked_specification_blocks = BTreeSet::new();
        for (bb, block) in body.basic_blocks().iter_enumerated() {
            if is_marked_specification_block(block, &tcx) {
                marked_specification_blocks.insert(bb);
            }
        }

        let mut specification_blocks = marked_specification_blocks;
        // All blocks dominated by specification blocks are also specification
        // blocks.
        let dominators = body.dominators();
        for specification_block in specification_blocks.clone() {
            for bb in body.basic_blocks().indices() {
                if dominators.is_dominated_by(bb, specification_block) {
                    specification_blocks.insert(bb);
                }
            }
        }
        // All blocks unavoidably leading to specification blocks are also
        // specification blocks.
        let mut work_queue: Vec<_> = specification_blocks.iter().cloned().collect();
        let predecessors = body.predecessors();
        while let Some(specification_block) = work_queue.pop() {
            for &predecessor in &predecessors[specification_block] {
                if specification_blocks.contains(&predecessor) {
                    continue;
                }
                if body.successors(predecessor).all(|predecessor_successor| {
                    specification_blocks.contains(&predecessor_successor)
                }) {
                    work_queue.push(predecessor);
                    specification_blocks.insert(predecessor);
                }
            }
        }

        // Collect entry points.
        let mut specification_entry_blocks = BTreeSet::new();
        for bb in body.basic_blocks().indices() {
            if !specification_blocks.contains(&bb) {
                for successor in body.successors(bb) {
                    if specification_blocks.contains(&successor) {
                        specification_entry_blocks.insert(successor);
                    }
                }
            }
        }

        Self {
            specification_blocks,
            specification_entry_blocks,
        }
    }

    pub(super) fn entry_points(&self) -> impl Iterator<Item = mir::BasicBlock> + '_ {
        self.specification_entry_blocks.iter().cloned()
    }

    pub(super) fn is_specification_block(&self, bb: mir::BasicBlock) -> bool {
        self.specification_blocks.contains(&bb)
    }
}
