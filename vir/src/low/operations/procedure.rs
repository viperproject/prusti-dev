use super::super::{
    ast::statement::Statement,
    cfg::{BasicBlock, Label, ProcedureDecl},
};
use crate::common::cfg::Cfg;
use std::collections::BTreeMap;

// impl ProcedureDecl {
//     // // FIXME: Code duplication.
//     // pub fn get_topological_sort(&self) -> Vec<Label> {
//     //     if self.basic_blocks.is_empty() {
//     //         Vec::new()
//     //     } else {
//     //         let mut visited: BTreeMap<_, _> = self
//     //             .basic_blocks
//     //             .keys()
//     //             .map(|label| (label.clone(), false))
//     //             .collect();
//     //         let mut topo_sorted = Vec::<Label>::with_capacity(self.basic_blocks.len());
//     //         *visited.get_mut(&self.entry).unwrap() = true;
//     //         for label in self.basic_blocks.keys() {
//     //             if !visited[label] {
//     //                 self.topological_sort_impl(&mut visited, &mut topo_sorted, label);
//     //             }
//     //         }
//     //         topo_sorted.push(self.entry.clone());
//     //         topo_sorted.reverse();
//     //         topo_sorted
//     //     }
//     // }

//     // // FIXME: Code duplication.
//     // fn topological_sort_impl(
//     //     &self,
//     //     visited: &mut BTreeMap<Label, bool>,
//     //     topo_sorted: &mut Vec<Label>,
//     //     current_label: &Label,
//     // ) {
//     //     assert!(!visited[current_label]);
//     //     *visited.get_mut(current_label).unwrap() = true;
//     //     let current_block = &self.basic_blocks[current_label];
//     //     for block_index in current_block.successor.get_following() {
//     //         if !visited[block_index] {
//     //             self.topological_sort_impl(visited, topo_sorted, block_index);
//     //         }
//     //     }
//     //     topo_sorted.push(current_label.clone())
//     // }
// }

impl Cfg for ProcedureDecl {
    type BasicBlockId = Label;
    type BasicBlock = BasicBlock;
    type Statement = Statement;
    type BasicBlockIdIterator<'a> =
        std::collections::btree_map::Keys<'a, Self::BasicBlockId, Self::BasicBlock>;

    fn entry(&self) -> &Self::BasicBlockId {
        &self.entry
    }

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
