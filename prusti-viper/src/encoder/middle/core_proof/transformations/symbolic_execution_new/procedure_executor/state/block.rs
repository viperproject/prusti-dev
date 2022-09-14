use std::collections::{BTreeMap, BTreeSet};

use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::{
        encoder_context::EncoderContext,
        symbolic_execution_new::{
            expression_interner::ExpressionInterner,
            procedure_executor::{
                block_marker_conditions::BlockMarkerCondition,
                constraints::BlockConstraints,
                heap::{BlockHeap, GlobalHeapState, HeapMergeReport},
            },
            program_context::ProgramContext,
        },
    },
};
use vir_crate::low::{self as vir_low};

#[derive(Clone)]
pub(in super::super) struct State {
    pub(in super::super) heap: BlockHeap,
    pub(in super::super) constraints: BlockConstraints,
}

impl State {
    pub(super) fn new(
        program_context: &ProgramContext<impl EncoderContext>,
    ) -> SpannedEncodingResult<Self> {
        Ok(Self {
            heap: Default::default(),
            constraints: BlockConstraints::new(program_context)?,
        })
    }

    pub(super) fn merge(
        &mut self,
        other: &Self,
        self_edge_block: &mut Vec<vir_low::Statement>,
        other_edge_block: &mut Vec<vir_low::Statement>,
        position: vir_low::Position,
        heap_merge_report: &mut HeapMergeReport,
        expression_interner: &mut ExpressionInterner,
        program_context: &ProgramContext<impl EncoderContext>,
        global_state: &mut GlobalHeapState,
    ) -> SpannedEncodingResult<()> {
        let merge_report = self.constraints.merge(&other.constraints)?;
        self.heap.merge(
            &other.heap,
            self_edge_block,
            other_edge_block,
            position,
            merge_report,
            heap_merge_report,
            &mut self.constraints,
            expression_interner,
            program_context,
            global_state,
        )?;
        Ok(())
    }

    // pub(super) fn get_dead_lifetime_equality_classes(
    //     &self,
    // ) -> SpannedEncodingResult<BTreeMap<String, BTreeSet<String>>> {
    //     self.heap
    //         .get_dead_lifetime_equality_classes(&self.constraints)
    // }

    // pub(super) fn remap_lifetimes(
    //     &mut self,
    //     remaps: BTreeMap<String, String>,
    // ) -> SpannedEncodingResult<()> {
    //     self.heap.remap_lifetimes(remaps)
    // }
}
