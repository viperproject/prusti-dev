use super::{ExecutionTraceBlock, ExecutionTraceBuilder};
use crate::encoder::middle::core_proof::transformations::symbolic_execution::heap::HeapEntry;
use vir_crate::low::{self as vir_low};

pub(in super::super) struct ExecutionTraceHeapView<'a> {
    pub(super) trace: &'a ExecutionTraceBuilder<'a>,
}

pub(in super::super) struct BlockView<'a> {
    block: &'a ExecutionTraceBlock,
}

impl<'a> ExecutionTraceHeapView<'a> {
    pub(in super::super) fn iter_blocks(&self) -> impl Iterator<Item = BlockView<'a>> {
        self.trace.blocks.iter().map(|block| BlockView { block })
    }

    pub(in super::super) fn block_count(&self) -> usize {
        self.trace.blocks.len()
    }

    pub(in super::super) fn last_block_id(&self) -> usize {
        self.trace.blocks.len() - 1
    }

    pub(in super::super) fn last_block_entry_count(&self) -> usize {
        self.trace.blocks.last().unwrap().heap_statements.len()
    }

    pub(in super::super) fn get_block(&self, id: usize) -> BlockView<'a> {
        BlockView {
            block: &self.trace.blocks[id],
        }
    }
}

impl<'a> BlockView<'a> {
    pub(in super::super) fn iter_entries(&self) -> impl Iterator<Item = &'a HeapEntry> {
        self.block.heap_statements.iter()
    }

    pub(in super::super) fn parent(&self) -> Option<usize> {
        self.block.parent
    }

    pub(in super::super) fn get_new_variables(&self) -> &[vir_low::VariableDecl] {
        &self.block.new_variables
    }

    pub(in super::super) fn get_new_labels(&self) -> &[vir_low::Label] {
        &self.block.new_labels
    }

    pub(crate) fn set_finalized_statements(&self, new_statements: &[vir_low::Statement]) {
        let mut borrow = self.block.finalized_statements.borrow_mut();
        if let Some(statements) = borrow.as_ref() {
            // FIXME: This does not work because whether an inhale is purified
            // out depends on whether a matching exhale is found, which depends
            // on the executed trace.
            for (old, new) in statements.iter().zip(new_statements.iter()) {
                assert_eq!(old, new);
            }
            assert_eq!(statements.len(), new_statements.len());
        } else {
            *borrow = Some(new_statements.to_vec());
        }
    }
}
