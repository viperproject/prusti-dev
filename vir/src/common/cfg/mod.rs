use std::collections::BTreeMap;

pub trait Cfg: Sized {
    type BasicBlockId: Ord + Clone;
    type BasicBlock: Clone;
    type Statement: Clone;
    type BasicBlockIdIterator<'a>: Iterator<Item = &'a Self::BasicBlockId>
    where
        Self: 'a;

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
