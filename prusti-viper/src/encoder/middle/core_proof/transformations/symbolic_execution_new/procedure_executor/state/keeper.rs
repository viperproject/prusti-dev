use super::block::State;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::{
        encoder_context::EncoderContext,
        symbolic_execution_new::{
            expression_interner::ExpressionInterner,
            procedure_executor::heap::{GlobalHeapState, HeapMergeReport},
            program_context::ProgramContext,
            trace_builder::TraceBuilder,
        },
    },
};
use prusti_common::config;
use std::collections::{BTreeMap, VecDeque};
use vir_crate::low::{self as vir_low};

#[derive(Default)]
pub(in super::super) struct StateKeeper {
    pub(super) states: BTreeMap<vir_low::Label, State>,
}

impl StateKeeper {
    pub(super) fn create_state_for_block(
        &mut self,
        new_block: &vir_low::Label,
        predecessors: &[vir_low::Label],
        expression_interner: &mut ExpressionInterner,
        program_context: &ProgramContext<impl EncoderContext>,
        global_state: &mut GlobalHeapState,
        trace_builder: &mut TraceBuilder,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        match predecessors.len() {
            0 => {
                self.states
                    .insert(new_block.clone(), State::new(program_context)?);
            }
            1 => {
                let predecessor = &predecessors[0];
                let predecessor_state = self.states.get(predecessor).unwrap();
                let state = predecessor_state.clone();
                self.states.insert(new_block.clone(), state);
            }
            _ => {
                // {
                //     let mut lifetime_equality_classes = Vec::new();
                //     for predecessor in predecessors {
                //         let predecessor_state = self.states.get(predecessor).unwrap();
                //         lifetime_equality_classes
                //             .push(predecessor_state.get_dead_lifetime_equality_classes()?);
                //     }
                //     // Iterate over mutable slices that start at ith element and
                //     // go till the end.
                //     let mut lifetime_equality_slice = &mut lifetime_equality_classes[..];
                //     while let Some((first_predecessor, tail)) =
                //         lifetime_equality_slice.split_first_mut()
                //     {
                //         for second_predecessor in &mut *tail {
                //             // Intersect matching equality classes.
                //             for first_class in first_predecessor.values_mut() {
                //                 assert!(!first_class.is_empty());
                //                 for second_class in second_predecessor.values_mut() {
                //                     assert!(!second_class.is_empty());
                //                     if !first_class.is_disjoint(second_class) {
                //                         first_class
                //                             .retain(|element| second_class.contains(element));
                //                         assert!(!first_class.is_empty());
                //                         second_class
                //                             .retain(|element| first_class.contains(element));
                //                         assert!(!second_class.is_empty());
                //                     }
                //                 }
                //             }
                //         }
                //         lifetime_equality_slice = tail;
                //     }

                //     // Pick a representative element from each set as the chosen remap target.
                //     let mut lifetime_predecessor_remaps = Vec::new();
                //     for equality_classes in lifetime_equality_classes {
                //         let mut lifetime_remaps = BTreeMap::new();
                //         for (lifetime, mut equality_class) in equality_classes {
                //             lifetime_remaps.insert(lifetime, equality_class.pop_first().unwrap());
                //         }
                //         lifetime_predecessor_remaps.push(lifetime_remaps);
                //     }

                //     // Remap all lifetime resources.
                //     assert_eq!(predecessors.len(), lifetime_predecessor_remaps.len());
                //     for (predecessor, remaps) in
                //         predecessors.iter().zip(lifetime_predecessor_remaps)
                //     {
                //         let predecessor_state = self.states.get_mut(predecessor).unwrap();
                //         predecessor_state.remap_lifetimes(remaps)?;
                //     }
                // };
                let mut predecessors_iter = predecessors.iter();
                let first_predecessor = predecessors_iter.next().unwrap();
                let mut first_predecessor_edge_block = Vec::new();
                let first_predecessor_state = self.states.get(first_predecessor).unwrap();
                let mut state = first_predecessor_state.clone();
                let mut heap_merge_report = HeapMergeReport::new();
                let mut predecessor_edge_blocks = VecDeque::new();
                for predecessor in predecessors_iter {
                    heap_merge_report.create_predecessor();
                    let predecessor_state = self.states.get(predecessor).unwrap();
                    let mut predecessor_edge_block = Vec::new();
                    state.merge(
                        predecessor_state,
                        &mut first_predecessor_edge_block,
                        &mut predecessor_edge_block,
                        position,
                        &mut heap_merge_report,
                        expression_interner,
                        program_context,
                        global_state,
                    )?;
                    predecessor_edge_blocks.push_back(predecessor_edge_block);
                }
                predecessor_edge_blocks.push_front(first_predecessor_edge_block);
                heap_merge_report.validate();
                let predecessor_statements = heap_merge_report.into_remap_statements(position);
                assert_eq!(predecessor_statements.len(), predecessors.len());
                assert_eq!(predecessor_edge_blocks.len(), predecessors.len());
                for (predecessor, (mut predecessor_edge_block, statements)) in
                    predecessors.iter().zip(
                        predecessor_edge_blocks
                            .into_iter()
                            .zip(predecessor_statements.into_iter()),
                    )
                {
                    predecessor_edge_block.extend(statements);
                    trace_builder.add_edge_block(
                        predecessor.clone(),
                        new_block.clone(),
                        predecessor_edge_block,
                    )?;
                }
                self.states.insert(new_block.clone(), state);
            }
        }
        Ok(())
    }

    pub(super) fn finalize_block(
        &mut self,
        block: &vir_low::Label,
        _expression_interner: &mut ExpressionInterner,
    ) -> SpannedEncodingResult<()> {
        let state = self.get_state_mut(block);
        state.constraints.set_visited_block(block.clone());
        state.heap.finalize_block(&mut state.constraints)?;
        Ok(())
    }

    pub(in super::super) fn get_state_mut(&mut self, block: &vir_low::Label) -> &mut State {
        self.states.get_mut(block).unwrap()
    }

    pub(in super::super) fn get_state(&self, block: &vir_low::Label) -> &State {
        self.states.get(block).unwrap()
    }

    pub(in super::super) fn uninitialize(
        &mut self,
        return_blocks: &[vir_low::Label],
    ) -> SpannedEncodingResult<()> {
        for return_block in return_blocks {
            let heap_block = self.get_state(return_block);
            if config::symbolic_execution_leak_check() {
                heap_block.heap.leak_check()?;
            }
        }
        std::mem::take(&mut self.states);
        Ok(())
    }
}
