use crate::high as vir_high;

impl super::Cfg for vir_high::ProcedureDecl {
    type BasicBlockId = vir_high::BasicBlockId;
    type BasicBlock = vir_high::BasicBlock;
    type Statement = vir_high::Statement;
    type BasicBlockIdIterator<'a> =
        std::collections::btree_map::Keys<'a, Self::BasicBlockId, Self::BasicBlock>;

    fn get_basic_block(&self, bb: &Self::BasicBlockId) -> Option<&Self::BasicBlock> {
        self.basic_blocks.get(bb)
    }

    fn get_basic_block_statement<'a>(
        &'a self,
        block: &'a Self::BasicBlock,
        statement_index: usize,
    ) -> Option<&'a Self::Statement> {
        block.statements.get(statement_index)
    }

    fn iter_basic_block_ids(&self) -> Self::BasicBlockIdIterator<'_> {
        self.basic_blocks.keys()
    }

    fn successors(&self, bb: &Self::BasicBlockId) -> Vec<&Self::BasicBlockId> {
        self.basic_blocks[bb].successor.get_following()
    }
}
