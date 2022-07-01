use prusti_interface::environment::{
    is_loop_invariant_block, is_marked_specification_block, Procedure,
};
use prusti_rustc_interface::{
    data_structures::graph::WithSuccessors,
    middle::{mir, ty::TyCtxt},
};
use std::collections::{BTreeMap, BTreeSet};

/// Information about the specification blocks.
pub(super) struct SpecificationBlocks {
    /// All blocks that are generated as a result of specification type-checking.
    specification_blocks: BTreeSet<mir::BasicBlock>,
    /// Blocks through which specifications are entered.
    specification_entry_blocks: BTreeSet<mir::BasicBlock>,
    /// A set of blocks containing the loop invariant of a given loop in
    /// execution order.
    ///
    /// FIXME: Add a check that ensure that the blocks are one after another.
    loop_invariant_blocks: BTreeMap<mir::BasicBlock, LoopInvariantBlocks>,
}

/// Information about loop invariant.
#[derive(Debug, Clone)]
pub(super) struct LoopInvariantBlocks {
    /// After which block the loop invariant should be inserted.
    pub(super) location: mir::BasicBlock,
    /// The blocks containing specification closures.
    pub(super) specification_blocks: Vec<mir::BasicBlock>,
}

impl SpecificationBlocks {
    pub(super) fn build<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
        procedure: &Procedure<'tcx>,
    ) -> Self {
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

        // Collect loop invariant blocks.
        let loop_info = procedure.loop_info();
        let predecessors = body.predecessors();
        let mut loop_invariant_blocks = BTreeMap::<_, LoopInvariantBlocks>::new();
        let mut loop_invariant_blocks_flat = BTreeSet::new();
        // We use reverse_postorder here because we need to make sure that we
        // preserve the order of invariants in which they were specified by the
        // user.
        for (bb, data) in prusti_rustc_interface::middle::mir::traversal::reverse_postorder(body) {
            if specification_blocks.contains(&bb) && is_loop_invariant_block(data, tcx) {
                let loop_head = loop_info.get_loop_head(bb).unwrap();
                let loop_blocks = loop_invariant_blocks.entry(loop_head).or_insert_with(|| {
                    assert_eq!(
                        predecessors[bb].len(),
                        1,
                        "The body_invariant should have exactly one predecessor block"
                    );
                    LoopInvariantBlocks {
                        location: predecessors[bb][0],
                        specification_blocks: Vec::new(),
                    }
                });
                loop_blocks.specification_blocks.push(bb);
                loop_invariant_blocks_flat.insert(bb);
            }
        }

        // Collect entry points.
        let mut specification_entry_blocks = BTreeSet::new();
        for bb in body.basic_blocks().indices() {
            if !specification_blocks.contains(&bb) {
                for successor in body.successors(bb) {
                    if specification_blocks.contains(&successor)
                        && !loop_invariant_blocks_flat.contains(&successor)
                    {
                        specification_entry_blocks.insert(successor);
                    }
                }
            }
        }

        Self {
            specification_blocks,
            specification_entry_blocks,
            loop_invariant_blocks,
        }
    }

    pub(super) fn entry_points(&self) -> impl Iterator<Item = mir::BasicBlock> + '_ {
        self.specification_entry_blocks.iter().cloned()
    }

    pub(super) fn is_specification_block(&self, bb: mir::BasicBlock) -> bool {
        self.specification_blocks.contains(&bb)
    }

    pub(super) fn loop_invariant_blocks(&self) -> &BTreeMap<mir::BasicBlock, LoopInvariantBlocks> {
        &self.loop_invariant_blocks
    }
}
