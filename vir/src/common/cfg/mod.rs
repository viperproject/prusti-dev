use std::collections::{BTreeMap, BTreeSet};

pub trait Cfg: Sized {
    type BasicBlockId: PartialEq + Eq + PartialOrd + Ord + Clone;
    type BasicBlock: Clone;
    type Statement: Clone;
    type BasicBlockIdIterator<'a>: Iterator<Item = &'a Self::BasicBlockId>
    where
        Self: 'a;

    fn entry(&self) -> &Self::BasicBlockId;

    fn get_basic_block(&self, bb: &Self::BasicBlockId) -> Option<&Self::BasicBlock>;

    fn get_basic_block_statement<'a>(
        &'a self,
        block: &'a Self::BasicBlock,
        statement_index: usize,
    ) -> Option<&'a Self::Statement>;

    fn iter_basic_block_ids(&self) -> Self::BasicBlockIdIterator<'_>;

    fn successors(&self, bb: &Self::BasicBlockId) -> Vec<&Self::BasicBlockId>;

    fn predecessors(&self) -> BTreeMap<&Self::BasicBlockId, Vec<&Self::BasicBlockId>> {
        let mut predecessors: BTreeMap<_, _> = self
            .iter_basic_block_ids()
            .map(|bb| (bb, Vec::new()))
            .collect();
        for bb in self.iter_basic_block_ids() {
            for successor in self.successors(bb) {
                predecessors.get_mut(successor).unwrap().push(bb);
            }
        }
        predecessors
    }

    fn predecessors_owned(&self) -> BTreeMap<Self::BasicBlockId, Vec<Self::BasicBlockId>> {
        self.predecessors()
            .into_iter()
            .map(|(label, predecessors)| {
                (label.clone(), predecessors.into_iter().cloned().collect())
            })
            .collect()
    }

    fn iter_basic_blocks(&self) -> CfgBasicBlockIterator<'_, Self> {
        let basic_block_id_iterator = self.iter_basic_block_ids();
        CfgBasicBlockIterator {
            cfg: self,
            basic_block_id_iterator,
        }
    }

    fn iter_statements(&self) -> CfgStatementIterator<'_, Self> {
        let mut basic_block_iterator = self.iter_basic_blocks();
        let current_block = basic_block_iterator.next();
        CfgStatementIterator {
            cfg: self,
            basic_block_iterator,
            current_block,
            current_statement: 0,
        }
    }

    fn get_topological_sort(&self) -> Vec<Self::BasicBlockId> {
        let mut visited: BTreeMap<_, _> = self
            .iter_basic_block_ids()
            .map(|bb| (bb.clone(), false))
            .collect();
        let len = visited.len();
        if len == 0 {
            return Vec::new();
        }
        let mut topo_sorted = Vec::<Self::BasicBlockId>::with_capacity(len);
        *visited.get_mut(self.entry()).unwrap() = true;
        for bb in self.iter_basic_block_ids() {
            if !visited[bb] {
                self.topological_sort_impl(&mut visited, &mut topo_sorted, bb);
            }
        }
        topo_sorted.push(self.entry().clone());
        topo_sorted.reverse();
        topo_sorted
    }

    fn topological_sort_impl(
        &self,
        visited: &mut BTreeMap<Self::BasicBlockId, bool>,
        topo_sorted: &mut Vec<Self::BasicBlockId>,
        current_block: &Self::BasicBlockId,
    ) {
        assert!(!visited[current_block]);
        *visited.get_mut(current_block).unwrap() = true;
        for block_index in self.successors(current_block) {
            if !visited[block_index] {
                self.topological_sort_impl(visited, topo_sorted, block_index);
            }
        }
        topo_sorted.push(current_block.clone())
    }

    /// Compute the set of basic blocks that can reach the given target basic
    /// block without visiting the ignored basic blocks.
    fn find_reaching(
        &self,
        target_block: &Self::BasicBlockId,
        ignored_blocks: &BTreeSet<&Self::BasicBlockId>,
    ) -> BTreeSet<Self::BasicBlockId> {
        let predecessors = self.predecessors();
        let mut reaching = BTreeSet::new();
        let mut worklist = vec![target_block];
        while let Some(bb) = worklist.pop() {
            if !reaching.contains(bb) && !ignored_blocks.contains(bb) {
                reaching.insert(bb.clone());
                if let Some(predecessors) = predecessors.get(bb) {
                    worklist.extend(predecessors);
                }
            }
        }
        reaching
    }

    /// Compute the dominaors of the `target_block` considering only the basic
    /// blocks in `considered_blocks`.
    fn compute_dominators_considering(
        &self,
        target_block: &Self::BasicBlockId,
        considered_blocks: &BTreeSet<Self::BasicBlockId>,
    ) -> BTreeSet<Self::BasicBlockId> {
        let traversal_order = self.get_topological_sort();
        let predecessors = self.predecessors();
        let mut dominators = BTreeMap::new();
        let mut entry_dominators = BTreeSet::new();
        entry_dominators.insert(self.entry());
        dominators.insert(self.entry(), entry_dominators);
        for bb in &traversal_order {
            if !(target_block == bb) && (!considered_blocks.contains(bb) || bb == self.entry()) {
                continue;
            }
            let mut predecessor_dominators = predecessors
                .get(bb)
                .unwrap()
                .iter()
                .flat_map(|predecessor| dominators.get(predecessor));
            let mut new_dominators = predecessor_dominators.next().unwrap().clone();
            for dominator_set in predecessor_dominators {
                new_dominators.retain(|dominator| dominator_set.contains(dominator));
            }
            new_dominators.insert(bb);
            dominators.insert(bb, new_dominators);
        }
        dominators
            .remove(target_block)
            .unwrap()
            .iter()
            .map(|&bb| bb.clone())
            .collect()
    }
}

pub struct CfgBasicBlockIterator<'a, C: Cfg> {
    cfg: &'a C,
    basic_block_id_iterator: <C as Cfg>::BasicBlockIdIterator<'a>,
}

impl<'a, C: Cfg> Iterator for CfgBasicBlockIterator<'a, C> {
    type Item = (&'a C::BasicBlockId, &'a C::BasicBlock);

    fn next(&mut self) -> Option<Self::Item> {
        self.basic_block_id_iterator
            .next()
            .map(|bb| (bb, self.cfg.get_basic_block(bb).unwrap()))
    }
}

pub struct CfgStatementIterator<'a, C: Cfg> {
    cfg: &'a C,
    basic_block_iterator: CfgBasicBlockIterator<'a, C>,
    current_block: Option<(&'a C::BasicBlockId, &'a C::BasicBlock)>,
    current_statement: usize,
}

impl<'a, C: Cfg> Iterator for CfgStatementIterator<'a, C> {
    type Item = (&'a C::BasicBlockId, usize, &'a C::Statement);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((bb, block)) = &self.current_block {
            if let Some(current_statement) = self
                .cfg
                .get_basic_block_statement(block, self.current_statement)
            {
                let index = self.current_statement;
                self.current_statement += 1;
                return Some((bb, index, current_statement));
            } else {
                // Reached the last statement of the basic block.
                self.current_block = self.basic_block_iterator.next();
                self.current_statement = 0;
            }
        }
        None
    }
}
