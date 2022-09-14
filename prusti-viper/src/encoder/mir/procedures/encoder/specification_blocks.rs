use prusti_interface::{
    environment::{
        debug_utils::to_text::ToText, is_checked_block_begin_marker, is_checked_block_end_marker,
        is_ghost_begin_marker, is_ghost_end_marker, is_loop_invariant_block, is_loop_variant_block,
        is_marked_specification_block, is_specification_begin_marker, is_specification_end_marker,
        is_try_finally_begin_marker, is_try_finally_end_marker, EnvQuery, Procedure,
    },
    specs::typed::SpecificationId,
};
use prusti_rustc_interface::{data_structures::graph::WithSuccessors, middle::mir};
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::common::graphviz::{Graph, NodeBuilder};

struct SpecificationRegion {
    body: BTreeSet<mir::BasicBlock>,
    exit_target_block: mir::BasicBlock,
}

pub(super) struct TryFinallyRegion {
    entry_block: mir::BasicBlock,
    pub(super) regular_exit_target_block: mir::BasicBlock,
    pub(super) panic_exit_edges: BTreeSet<(mir::BasicBlock, mir::BasicBlock)>,
    pub(super) function_panic_exit_edges: BTreeSet<(mir::BasicBlock, mir::BasicBlock)>,
    body: BTreeSet<mir::BasicBlock>,
    pub(super) on_panic_specification_region_id: SpecificationId,
    pub(super) finally_specification_region_id: SpecificationId,
}

/// Information about the specification blocks.
pub struct SpecificationBlocks {
    /// All blocks that are generated as a result of specification type-checking.
    specification_blocks: BTreeSet<mir::BasicBlock>,
    /// Blocks through which specifications are entered.
    specification_entry_blocks: BTreeSet<mir::BasicBlock>,
    ghost_blocks: BTreeSet<mir::BasicBlock>,
    /// A region of specification blocks where key of the map indicates the
    /// entry block.
    specification_regions: BTreeMap<mir::BasicBlock, SpecificationRegion>,
    specification_regions_by_spec_ids: BTreeMap<SpecificationId, mir::BasicBlock>,
    /// `with_finally!` regions.
    try_finally_regions: Vec<TryFinallyRegion>,
    /// The set of blocks in which we should check the preconditions of called
    /// functions even in memory safety mode.
    checked_blocks: BTreeSet<mir::BasicBlock>,
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
    #[tracing::instrument(name = "SpecificationBlocks::build", level = "debug", skip_all)]
    pub fn build<'tcx>(
        env_query: EnvQuery<'tcx>,
        body: &mir::Body<'tcx>,
        procedure: Option<&Procedure<'tcx>>,
        collect_loop_invariants: bool,
    ) -> Self {
        // Blocks that contain closures marked with `#[spec_only]` attributes.
        let mut marked_specification_blocks = BTreeSet::new();
        for (bb, block) in body.basic_blocks.iter_enumerated() {
            if is_marked_specification_block(env_query, block) {
                marked_specification_blocks.insert(bb);
            }
        }

        let mut specification_blocks = marked_specification_blocks;
        // All blocks dominated by specification blocks are also specification
        // blocks.
        let dominators = body.basic_blocks.dominators();
        for specification_block in specification_blocks.clone() {
            for bb in body.basic_blocks.indices() {
                if dominators.dominates(specification_block, bb) {
                    specification_blocks.insert(bb);
                }
            }
        }
        // All blocks unavoidably leading to specification blocks are also
        // specification blocks.
        let mut work_queue: Vec<_> = specification_blocks.iter().cloned().collect();
        let predecessors = body.basic_blocks.predecessors();
        while let Some(specification_block) = work_queue.pop() {
            for &predecessor in &predecessors[specification_block] {
                if specification_blocks.contains(&predecessor) {
                    continue;
                }
                if body
                    .basic_blocks
                    .successors(predecessor)
                    .all(|predecessor_successor| {
                        specification_blocks.contains(&predecessor_successor)
                    })
                {
                    work_queue.push(predecessor);
                    specification_blocks.insert(predecessor);
                }
            }
        }

        // Collect loop invariant blocks.
        let mut loop_invariant_blocks = BTreeMap::<_, LoopInvariantBlocks>::new();
        let mut loop_spec_blocks_flat = BTreeSet::new();
        if collect_loop_invariants {
            let loop_info = procedure
                .expect("procedure needs to be Some when collect_loop_invariants is true")
                .loop_info();
            let predecessors = body.basic_blocks.predecessors();
            // We use reverse_postorder here because we need to make sure that we
            // preserve the order of invariants in which they were specified by the
            // user.
            for (bb, data) in
                prusti_rustc_interface::middle::mir::traversal::reverse_postorder(body)
            {
                if specification_blocks.contains(&bb)
                    && (is_loop_invariant_block(env_query, data)
                        || is_loop_variant_block(env_query, data))
                {
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
                    loop_spec_blocks_flat.insert(bb);
                }
            }
        }

        // Collect `with_finally!` regions.
        let mut try_finally_regions = Vec::new();
        {
            for (bb, data) in mir::traversal::reverse_postorder(body) {
                if let Some((on_panic_specification_region_id, finally_specification_region_id)) =
                    is_try_finally_begin_marker(env_query, data)
                {
                    let region = collect_try_finally_region(
                        env_query,
                        body,
                        bb,
                        on_panic_specification_region_id,
                        finally_specification_region_id,
                    );
                    try_finally_regions.push(region);
                }
            }
        }

        let mut checked_blocks = BTreeSet::new();
        {
            for (bb, data) in mir::traversal::reverse_postorder(body) {
                if is_checked_block_begin_marker(env_query, data) {
                    collect_checked_region(env_query, body, bb, &mut checked_blocks);
                }
            }
        }

        // Collect specification regions. Specification regions are all blocks
        // that are reachable from a block containing
        // `prusti_specification_begin` marker without going through the
        // corresponding `prusti_specification_end` marker.
        let mut all_specification_region_blocks = BTreeSet::new();
        let mut specification_regions = BTreeMap::new();
        let mut specification_regions_by_spec_ids = BTreeMap::new();
        {
            for (bb, data) in mir::traversal::reverse_postorder(body) {
                if let Some(spec_id) = is_specification_begin_marker(env_query, data) {
                    let (region, exit_target_block) = collect_specification_region(
                        env_query,
                        body,
                        bb,
                        &mut all_specification_region_blocks,
                    );
                    specification_blocks.extend(region.iter().cloned());
                    // Check that the `region` is a subset of `specification_blocks`.
                    assert!(
                        region.is_subset(&specification_blocks),
                        "{:?} ⊆ {:?}",
                        region,
                        specification_blocks
                    );
                    assert!(specification_regions_by_spec_ids
                        .insert(spec_id, bb)
                        .is_none());
                    assert!(specification_regions
                        .insert(
                            bb,
                            SpecificationRegion {
                                body: region,
                                exit_target_block
                            }
                        )
                        .is_none());
                }
            }
        }

        // Collect entry points.
        let mut specification_entry_blocks = BTreeSet::new();
        for bb in body.basic_blocks.indices() {
            if !specification_blocks.contains(&bb) {
                for successor in body.basic_blocks.successors(bb) {
                    if specification_blocks.contains(&successor)
                        && !loop_spec_blocks_flat.contains(&successor)
                        && !all_specification_region_blocks.contains(&successor)
                    {
                        specification_entry_blocks.insert(successor);
                    }
                }
            }
        }

        // collect ghost blocks
        // ghost blocks are all the blocks that are reachable from a block containing a ghost_begin marking
        // without going through the corresponding ghost_end marking
        let mut ghost_blocks = BTreeSet::new();
        {
            let mut queue = Vec::new();

            for (bb, data) in mir::traversal::reverse_postorder(body) {
                if is_ghost_begin_marker(env_query, data)
                    && !all_specification_region_blocks.contains(&bb)
                {
                    queue.push(bb);
                }
                if is_ghost_end_marker(env_query, data)
                    && !all_specification_region_blocks.contains(&bb)
                {
                    ghost_blocks.insert(bb);
                }
            }

            while let Some(bb) = queue.pop() {
                if ghost_blocks.contains(&bb) {
                    continue;
                }
                let data = &body.basic_blocks[bb];
                ghost_blocks.insert(bb);

                // end marker is only conditionally reachable, as it is inside an `if false {}`
                // However, if a block has the end marker as successor, the other successors will be outside the ghost block, and shall be ignored.
                let before_end = data
                    .terminator()
                    .successors()
                    .any(|bb| is_ghost_end_marker(env_query, &body.basic_blocks[bb]));

                for succ in data.terminator.iter().flat_map(|t| t.successors()) {
                    if before_end {
                        ghost_blocks.insert(succ);
                    } else {
                        queue.push(succ);
                    }
                }
            }
        }

        Self {
            specification_blocks,
            specification_entry_blocks,
            loop_invariant_blocks,
            specification_regions,
            specification_regions_by_spec_ids,
            ghost_blocks,
            try_finally_regions,
            checked_blocks,
        }
    }

    pub fn entry_points(&self) -> impl Iterator<Item = mir::BasicBlock> + '_ {
        self.specification_entry_blocks.iter().cloned()
    }

    pub fn take_specification_regions(
        &mut self,
    ) -> impl Iterator<Item = (mir::BasicBlock, mir::BasicBlock, BTreeSet<mir::BasicBlock>)> {
        std::mem::take(&mut self.specification_regions)
            .into_iter()
            .map(
                |(
                    entry,
                    SpecificationRegion {
                        body: region,
                        exit_target_block: exit,
                    },
                )| (entry, exit, region),
            )
    }

    pub fn is_specification_block(&self, bb: mir::BasicBlock) -> bool {
        self.specification_blocks.contains(&bb)
    }

    pub(super) fn is_ghost_block(&self, bb: mir::BasicBlock) -> bool {
        self.ghost_blocks.contains(&bb)
    }

    pub(super) fn loop_invariant_blocks(&self) -> &BTreeMap<mir::BasicBlock, LoopInvariantBlocks> {
        &self.loop_invariant_blocks
    }

    pub(super) fn ghost_blocks(&self) -> &BTreeSet<mir::BasicBlock> {
        &self.ghost_blocks
    }

    pub(super) fn try_finally_regions(&self) -> &[TryFinallyRegion] {
        &self.try_finally_regions
    }

    pub(super) fn spec_id_to_entry_block(&self, spec_id: &SpecificationId) -> mir::BasicBlock {
        self.specification_regions_by_spec_ids[spec_id]
    }

    pub(super) fn is_checked(&self, bb: mir::BasicBlock) -> bool {
        self.checked_blocks.contains(&bb)
    }
}

fn collect_try_finally_region(
    env_query: EnvQuery,
    body: &mir::Body,
    entry_block: mir::BasicBlock,
    on_panic_specification_region_id: SpecificationId,
    finally_specification_region_id: SpecificationId,
) -> TryFinallyRegion {
    let mut region = BTreeSet::new();
    let mut work_queue = vec![entry_block];
    let mut end_blocks = Vec::new();
    let mut panic_exit_edges = BTreeSet::new();
    let mut function_panic_exit_edges = BTreeSet::new();
    while let Some(bb) = work_queue.pop() {
        if region.contains(&bb) {
            continue;
        }
        region.insert(bb);
        let data = &body.basic_blocks[bb];
        let before_end = data
            .terminator()
            .successors()
            .any(|bb| is_try_finally_end_marker(env_query, &body.basic_blocks[bb]));
        for succ in data.terminator().successors() {
            let mut add_succ = || {
                if before_end {
                    region.insert(succ);
                    end_blocks.push(succ);
                } else {
                    work_queue.push(succ);
                }
            };
            if let Some(Some(unwind)) = data.terminator().unwind() {
                if succ != *unwind {
                    add_succ();
                } else if let mir::TerminatorKind::Call { .. } = data.terminator().kind {
                    function_panic_exit_edges.insert((bb, succ));
                } else {
                    panic_exit_edges.insert((bb, succ));
                }
            } else {
                add_succ();
            }
        }
    }
    let regular_exit_target_block = find_exit_target_block(body, end_blocks);
    TryFinallyRegion {
        entry_block,
        regular_exit_target_block,
        panic_exit_edges,
        function_panic_exit_edges,
        body: region,
        on_panic_specification_region_id,
        finally_specification_region_id,
    }
}

fn collect_checked_region(
    env_query: EnvQuery,
    body: &mir::Body,
    entry_block: mir::BasicBlock,
    checked_blocks: &mut BTreeSet<mir::BasicBlock>,
) {
    let mut work_queue = vec![entry_block];
    while let Some(bb) = work_queue.pop() {
        if checked_blocks.contains(&bb) {
            continue;
        }
        checked_blocks.insert(bb);
        let data = &body.basic_blocks[bb];
        let before_end = data
            .terminator()
            .successors()
            .any(|bb| is_checked_block_end_marker(env_query, &body.basic_blocks[bb]));
        for succ in data.terminator().successors() {
            if before_end {
                checked_blocks.insert(succ);
            } else {
                work_queue.push(succ);
            }
        }
    }
}

fn collect_specification_region(
    env_query: EnvQuery,
    body: &mir::Body,
    entry_block: mir::BasicBlock,
    all_specification_region_blocks: &mut BTreeSet<mir::BasicBlock>,
) -> (BTreeSet<mir::BasicBlock>, mir::BasicBlock) {
    let mut region = BTreeSet::new();
    let mut work_queue = vec![entry_block];
    let mut end_blocks = Vec::new();
    while let Some(bb) = work_queue.pop() {
        if region.contains(&bb) {
            continue;
        }
        region.insert(bb);
        all_specification_region_blocks.insert(bb);
        let data = &body.basic_blocks[bb];
        let before_end = data
            .terminator()
            .successors()
            .any(|bb| is_specification_end_marker(env_query, &body.basic_blocks[bb]));
        for succ in data.terminator().successors() {
            let mut add_succ = || {
                if before_end {
                    region.insert(succ);
                    end_blocks.push(succ);
                } else {
                    work_queue.push(succ);
                }
            };
            if let Some(Some(unwind)) = data.terminator().unwind() {
                if succ != *unwind {
                    add_succ();
                }
            } else {
                add_succ();
            }
        }
    }
    // let get_jump_target = |block| {
    //     let mut iterator = body.basic_blocks[block].terminator().successors();
    //     let jump_target = iterator.next().unwrap();
    //     assert!(iterator.next().is_none());
    //     jump_target
    // };
    // let exit_target_block = get_jump_target(end_blocks.pop().unwrap());
    // while let Some(end_block) = end_blocks.pop() {
    //     assert_eq!(exit_target_block, get_jump_target(end_block));
    // }
    let exit_target_block = find_exit_target_block(body, end_blocks);
    (region, exit_target_block)
}

fn find_exit_target_block(
    body: &mir::Body,
    mut end_blocks: Vec<mir::BasicBlock>,
) -> mir::BasicBlock {
    let get_jump_target = |block| {
        let mut iterator = body.basic_blocks[block].terminator().successors();
        let jump_target = iterator.next().unwrap();
        assert!(iterator.next().is_none());
        jump_target
    };
    let exit_target_block = get_jump_target(end_blocks.pop().unwrap());
    while let Some(end_block) = end_blocks.pop() {
        assert_eq!(exit_target_block, get_jump_target(end_block));
    }
    exit_target_block
}

pub(super) fn specification_blocks_to_graph(
    body: &mir::Body,
    specification_blocks: &SpecificationBlocks,
) -> Graph {
    let mut graph = Graph::with_columns(&["location", "statement"]);
    for bb in body.basic_blocks.indices() {
        let style = if specification_blocks.is_specification_block(bb) {
            "bgcolor=\"green\""
        } else {
            "bgcolor=\"grey\""
        };
        let mut flags = String::new();
        if specification_blocks.specification_blocks.contains(&bb) {
            flags.push_str("spec_block ");
        }
        if specification_blocks
            .specification_entry_blocks
            .contains(&bb)
        {
            flags.push_str("spec_entry_block ");
        }
        if specification_blocks.ghost_blocks.contains(&bb) {
            flags.push_str("ghost_block ");
        }
        if specification_blocks.specification_regions.contains_key(&bb) {
            flags.push_str("spec_region_entry ");
        }
        for (entry, region) in &specification_blocks.specification_regions {
            if region.body.contains(&bb) {
                flags.push_str(&format!(
                    "spec_region({} → {}) ",
                    entry.index(),
                    region.exit_target_block.index()
                ));
            }
            if region.exit_target_block == bb {
                flags.push_str(&format!("spec_region_exit({}) ", entry.index()));
            }
        }
        for region in &specification_blocks.try_finally_regions {
            if region.entry_block == bb {
                flags.push_str(&format!(
                    "try_finally_region_entry({}) ",
                    region.finally_specification_region_id
                ));
            }
            if region.body.contains(&bb) {
                flags.push_str(&format!(
                    "try_finally_region({} → {}) ",
                    region.entry_block.index(),
                    region.regular_exit_target_block.index()
                ));
            }
            if region.regular_exit_target_block == bb {
                flags.push_str(&format!(
                    "try_finally_region_exit({}) ",
                    region.entry_block.index()
                ));
            }
            // if region.finally_specification_region == bb {
            //     flags.push_str(&format!(
            //         "finally_block({} → {}) ",
            //         region.entry_block.index(),
            //         region.regular_exit_target_block.index()
            //     ));
            // }
            if region
                .panic_exit_edges
                .iter()
                .any(|(_, exit_block)| exit_block == &bb)
            {
                flags.push_str(&format!(
                    "panic_exit_block({} → {}) ",
                    region.entry_block.index(),
                    region.regular_exit_target_block.index()
                ));
            }
        }
        let mut node_builder = graph.create_node_with_custom_style(bb.to_text(), style.to_string());
        node_builder.add_row_single(flags);
        let mir::BasicBlockData {
            statements,
            terminator,
            ..
        } = &body[bb];
        let mut location = mir::Location {
            block: bb,
            statement_index: 0,
        };
        let terminator_index = statements.len();
        while location.statement_index < terminator_index {
            specification_blocks_to_graph_statement(
                &mut node_builder,
                location,
                statements[location.statement_index].to_text(),
            );
            location.statement_index += 1;
        }
        if let Some(terminator) = terminator {
            specification_blocks_to_graph_statement(
                &mut node_builder,
                location,
                terminator.to_text(),
            );
        }
        node_builder.build();
        if let Some(terminator) = terminator {
            specification_blocks_to_graph_terminator(&mut graph, bb, terminator);
        }
    }
    graph
}

fn specification_blocks_to_graph_statement(
    node_builder: &mut NodeBuilder,
    location: mir::Location,
    statement_text: String,
) {
    let mut row_builder = node_builder.create_row();
    row_builder.set("location", location.to_text());
    row_builder.set("statement", statement_text);
    row_builder.build();
}

fn specification_blocks_to_graph_terminator(
    graph: &mut Graph,
    bb: mir::BasicBlock,
    terminator: &mir::Terminator<'_>,
) {
    terminator
        .successors()
        .for_each(|succ| graph.add_regular_edge(bb.to_text(), succ.to_text()));
}
