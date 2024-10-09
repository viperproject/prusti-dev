use prusti_rustc_interface::{
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId,
};
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Debug)]
pub(crate) struct Loop {
    pub head: mir::BasicBlock,
    pub back_edges: FxHashSet<mir::BasicBlock>,
    // span?, depth?
}

#[derive(Debug)]
pub(crate) struct LoopAnalysis {
    pub loops: FxHashMap<mir::BasicBlock, Loop>,
    pub back_edges: FxHashSet<(mir::BasicBlock, mir::BasicBlock)>,
}

pub(crate) struct LoopVisitor<'a, 'tcx: 'a> {
    body: &'a mir::Body<'tcx>,
    path: Vec<mir::BasicBlock>,
    in_path: IndexVec<mir::BasicBlock, bool>,
    loop_heads: IndexVec<mir::BasicBlock, Option<Loop>>,
}

impl LoopAnalysis {
    pub fn analyse(body: &mir::Body<'_>) -> Self {
        let block_count = body.basic_blocks.len();
        let mut analysis = LoopVisitor {
            body,
            path: vec![],
            in_path: IndexVec::from_elem_n(false, block_count),
            loop_heads: IndexVec::from_fn_n(|_| None, block_count),
        };
        analysis.walk_block(mir::START_BLOCK);
        let mut back_edges: FxHashSet<(mir::BasicBlock, mir::BasicBlock)> = Default::default();
        analysis.loop_heads
            .iter()
            .for_each(|e| if let Some(e) = e {
                for prev in &e.back_edges {
                    back_edges.insert((*prev, e.head));
                }
            });
        Self {
            loops: analysis.loop_heads
                .into_iter()
                .filter_map(|e| {
                    let e = e?;
                    Some((e.head, e))
                })
                .collect(),
            back_edges,
        }
    }
}

impl<'a, 'tcx: 'a> LoopVisitor<'a, 'tcx> {
    fn walk_block(
        &mut self,
        block: mir::BasicBlock,
        // depth: usize,
    ) {
        if self.in_path[block] {
            self.loop_heads[block]
                .get_or_insert(Loop {
                    head: block,
                    back_edges: Default::default(),
                })
                .back_edges
                .insert(self.path[self.path.len() - 2]);
            // TODO: find full loop sub-CFG?
            return;
        }
        self.in_path[block] = true;

        use prusti_rustc_interface::data_structures::graph::WithSuccessors;
        for succ in self.body.basic_blocks.successors(block) {
            self.path.push(succ);
            self.walk_block(succ);
            assert_eq!(self.path.pop().unwrap(), succ);
        }

        self.in_path[block] = false;
    }
}
