// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    index::{Idx, IndexVec},
    middle::mir::{BasicBlock, Body, START_BLOCK}
};

#[derive(Clone, Debug)]
struct LoopSet {
    // Tracks up to 64 loops inline
    data: smallvec::SmallVec<[u8; 8]>,
}
impl LoopSet {
    const OFFSET: usize = 8 * std::mem::size_of::<u8>();

    fn new() -> Self {
        Self {
            data: smallvec::SmallVec::from_const([0; 8]),
        }
    }
    fn add(&mut self, loop_idx: LoopId) {
        let loop_idx = loop_idx.index();
        let idx = loop_idx / Self::OFFSET;
        if idx >= self.data.len() {
            self.data.resize(idx + 1, 0);
        }
        self.data[idx] |= 1 << (loop_idx % Self::OFFSET);
    }
    fn merge(&mut self, other: &Self) {
        if other.data.len() > self.data.len() {
            self.data.resize(other.data.len(), 0);
        }
        for (idx, val) in other.data.iter().enumerate() {
            self.data[idx] |= val;
        }
    }
    fn clear(&mut self, loop_idx: LoopId) {
        let loop_idx = loop_idx.index();
        let idx = loop_idx / Self::OFFSET;
        assert!(idx < self.data.len());
        self.data[idx] &= !(1 << (loop_idx % Self::OFFSET));
    }
    fn iter(&self) -> impl DoubleEndedIterator<Item = LoopId> + '_ {
        self.data
            .iter()
            .enumerate()
            .flat_map(|(idx, &val)| {
                let to = if val == 0 { 0 } else { Self::OFFSET };
                (0..to)
                    .filter(move |&i| val & (1 << i) != 0)
                    .map(move |i| LoopId::new(idx * Self::OFFSET + i))
        })
    }
}

#[derive(Debug)]
pub struct LoopAnalysis {
    bb_data: IndexVec<BasicBlock, LoopSet>,
    loop_heads: IndexVec<LoopId, BasicBlock>,
}

impl LoopAnalysis {
    pub fn find_loops(body: &Body) -> Self {
        let mut analysis = LoopAnalysis {
            bb_data: IndexVec::from_elem_n(LoopSet::new(), body.basic_blocks.len()),
            loop_heads: IndexVec::new(),
        };
        let raw_bb_data: *const _ = &analysis.bb_data;

        let mut visited_bbs: IndexVec<BasicBlock, bool> = IndexVec::from_elem_n(false, body.basic_blocks.len());

        let mut loop_head_bb_index: IndexVec<BasicBlock, LoopId> = IndexVec::from_elem_n(NO_LOOP, body.basic_blocks.len());
        for bb in body.basic_blocks.reverse_postorder().iter().copied().rev() {
            let data = &mut analysis.bb_data[bb];
            for succ in body.basic_blocks[bb].terminator().successors() {
                if visited_bbs[succ] {
                    // Merge in loops of this succ
                    assert_ne!(bb, succ);
                    // SAFETY: Index is different to mutably borrowed index
                    let other = unsafe { &(*raw_bb_data)[succ] };
                    data.merge(other);
                    // If `succ` is a loop head, we are no longer in that loop
                    let loop_idx = loop_head_bb_index[succ];
                    if loop_idx != NO_LOOP {
                        assert_eq!(analysis.loop_heads[loop_idx], succ);
                        data.clear(loop_idx);
                    }
                } else {
                    // Create new loop
                    let loop_idx = &mut loop_head_bb_index[succ];
                    if *loop_idx == NO_LOOP {
                        *loop_idx = LoopId::new(analysis.loop_heads.len());
                        analysis.loop_heads.push(succ);
                    }
                    data.add(*loop_idx);
                }
            }
            visited_bbs[bb] = true;
        }
        if cfg!(debug_assertions) {
            analysis.consistency_check();
        }
        analysis
    }
    pub fn loops(&self, bb: BasicBlock) -> impl DoubleEndedIterator<Item = LoopId> + '_ {
        self.bb_data[bb].iter()
    }
    pub fn loop_depth(&self, bb: BasicBlock) -> usize {
        self.loops(bb).count()
    }
    pub fn loop_nest_depth(&self, l: LoopId) -> usize {
        self.loop_depth(self[l]) - 1
    }
    /// Returns the loop which contains `bb` as well as all other loops of `bb`.
    pub fn outermost_loop(&self, bb: BasicBlock) -> Option<LoopId> {
        self.loops(bb).next()
    }
    /// Returns the loop which contains `bb` but no other loops of `bb`.
    pub fn innermost_loop(&self, bb: BasicBlock) -> Option<LoopId> {
        self.loops(bb).next_back()
    }

    fn consistency_check(&self) {
        // Start block can be in a maximum of one loop, of which it is the head
        let mut start_loops: Vec<_> = self.loops(START_BLOCK).collect();
        if let Some(l) = start_loops.pop() {
            assert_eq!(self[l], START_BLOCK);
        }
        assert!(start_loops.is_empty());
        // Check that `innermost_loop` and `outermost_loop` are correct (TODO: remove this check)
        for bb in self.bb_data.indices() {
            let innermost_depth = self.innermost_loop(bb).map(|l| self.loop_nest_depth(l)).unwrap_or_default();
            let outermost_depth = self.outermost_loop(bb).map(|l| self.loop_nest_depth(l)).unwrap_or_default();
            assert!(self.loops(bb).map(|l| self.loop_nest_depth(l)).all(|d| outermost_depth <= d && d <= innermost_depth));
        }
    }
}

impl std::ops::Index<LoopId> for LoopAnalysis {
    type Output = BasicBlock;
    fn index(&self, index: LoopId) -> &Self::Output {
        &self.loop_heads[index]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LoopId(usize);
impl Idx for LoopId {
    fn new(idx: usize) -> Self {
        Self(idx)
    }
    fn index(self) -> usize {
        self.0
    }
}
const NO_LOOP: LoopId = LoopId(usize::MAX);
