mod graphviz;
mod entry;
mod state;
mod finalizer;
mod predicate_snapshots;
mod lifetime_tokens;

use super::{
    program_context::ProgramContext,
    trace::Trace,
    trace_builder::{ExecutionTraceBuilder, ExecutionTraceHeapView},
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::encoder_context::EncoderContext,
};
use log::debug;
use prusti_common::config;
use vir_crate::low::{self as vir_low};

use self::finalizer::TraceFinalizer;
pub(super) use self::{entry::HeapEntry, state::HeapState};

impl<'a> ExecutionTraceBuilder<'a> {
    pub(super) fn heap_comment(
        &mut self,
        statement: vir_low::ast::statement::Comment,
    ) -> SpannedEncodingResult<()> {
        self.add_heap_entry(HeapEntry::Comment(statement))?;
        Ok(())
    }

    pub(super) fn heap_label(
        &mut self,
        statement: vir_low::ast::statement::Label,
    ) -> SpannedEncodingResult<()> {
        let state = self.current_heap_state_mut();
        state.save_state(statement.label.clone());
        self.add_heap_entry(HeapEntry::Label(statement))?;
        Ok(())
    }

    pub(super) fn heap_assume(
        &mut self,
        expression: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        assert!(
            !position.is_default(),
            "assume {expression} with default position"
        );
        self.add_heap_entry(HeapEntry::Assume(vir_low::ast::statement::Assume {
            expression,
            position,
        }))?;
        Ok(())
    }

    pub(super) fn heap_assert(
        &mut self,
        expression: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        self.add_heap_entry(HeapEntry::Assert(vir_low::ast::statement::Assert {
            expression,
            position,
        }))?;
        Ok(())
    }

    fn next_location(&self) -> Location {
        let view = self.heap_view();
        Location {
            block_id: view.block_count() - 1,
            entry_id: view.last_block_entry_count(),
        }
    }

    pub(super) fn heap_inhale_predicate(
        &mut self,
        predicate: vir_low::ast::expression::PredicateAccessPredicate,
        program: &ProgramContext<impl EncoderContext>,
        // is_instance_non_aliased: bool,
        // non_aliased_predicate_instances: &'a FxHashSet<vir_low::PredicateAccessPredicate>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let next_location = self.next_location();
        let (state, solver) = self.current_heap_and_egraph_state_mut();
        // let (state, solver) = self.current_heap_and_egraph_state_mut();
        // solver.saturate()?;
        // let mut is_instance_non_aliased = false;
        // for non_aliased_predicate in non_aliased_predicate_instances {
        //     if non_aliased_predicate.name == predicate.name {
        //         if arguments_match(
        //             &non_aliased_predicate.arguments,
        //             &predicate.arguments,
        //             solver,
        //         )? {
        //             is_instance_non_aliased = true;
        //             break;
        //         }
        //     }
        // }
        state.add_predicate_instance(
            solver,
            program,
            &predicate,
            //  is_instance_non_aliased,
            next_location,
        )?;
        self.add_heap_entry(HeapEntry::InhalePredicate(predicate, position))
    }

    pub(super) fn heap_inhale_generic(
        &mut self,
        expression: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let state = self.current_heap_state_mut();
        for predicate_name in expression.collect_access_predicate_names() {
            state.mark_predicate_instances_seen_qp_inhale(&predicate_name);
        }
        self.add_heap_entry(HeapEntry::InhaleGeneric(vir_low::ast::statement::Inhale {
            expression,
            position,
        }))
    }

    pub(super) fn heap_exhale_predicate(
        &mut self,
        predicate: vir_low::ast::expression::PredicateAccessPredicate,
        program: &mut ProgramContext<impl EncoderContext>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let next_location = self.next_location();
        let (state, solver) = self.current_heap_and_egraph_state_mut();
        let result = state.try_removing_predicate_instance(
            solver,
            program,
            &predicate,
            next_location,
            position,
        )?;
        if let state::PurificationResult::Error(error_position) = result {
            self.add_heap_entry(HeapEntry::Comment(vir_low::Comment {
                comment: format!("Failed to exhale non-aliased predicate: {}", predicate),
            }))?;
            self.add_heap_entry(HeapEntry::Assert(vir_low::Assert {
                expression: false.into(),
                position: error_position,
            }))?;
        }
        self.add_heap_entry(HeapEntry::ExhalePredicate(predicate, position))?;
        Ok(())
    }

    pub(super) fn heap_exhale_generic(
        &mut self,
        expression: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let state = self.current_heap_state_mut();
        for predicate_name in expression.collect_access_predicate_names() {
            state.mark_predicate_instances_seen_qp_exhale(&predicate_name);
        }
        self.add_heap_entry(HeapEntry::ExhaleGeneric(vir_low::ast::statement::Exhale {
            expression,
            position,
        }))
    }

    pub(super) fn heap_finalize_trace(
        &mut self,
        program: &ProgramContext<impl EncoderContext>,
        block_id: usize,
    ) -> SpannedEncodingResult<Trace> {
        debug!("Finalizing trace");
        // let (state, solver) = self.current_heap_and_egraph_state();
        let mut solver = self.steal_egraph_solver(block_id);
        let state = self.heap_state(block_id);
        let view = self.heap_view();
        // let last_block_id = view.last_block_id();
        let last_block_id = block_id;
        let mut trace_finalizer = TraceFinalizer::new(
            self.source_filename,
            self.procedure_name,
            state,
            &mut solver,
            program,
        );
        self.finalize_trace_for_block(&mut trace_finalizer, view, last_block_id)?;
        Ok(trace_finalizer.into_trace())
    }

    fn finalize_trace_for_block(
        &self,
        trace_finalizer: &mut TraceFinalizer<impl EncoderContext>,
        view: ExecutionTraceHeapView,
        block_id: usize,
    ) -> SpannedEncodingResult<()> {
        let block = view.get_block(block_id);
        if let Some(parent_id) = block.parent() {
            self.finalize_trace_for_block(trace_finalizer, view, parent_id)?;
        }
        trace_finalizer.add_variables(block.get_new_variables())?;
        trace_finalizer.add_labels(block.get_new_labels())?;
        let trace_checkpoint = trace_finalizer.trace_len();
        for (entry_id, entry) in block.iter_entries().enumerate() {
            trace_finalizer.add_entry(Location { block_id, entry_id }, entry)?;
        }
        let finalized_statements = trace_finalizer.trace_suffix(trace_checkpoint);
        if config::symbolic_execution_single_method() {
            block.set_finalized_statements(finalized_statements);
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Location {
    block_id: usize,
    entry_id: usize,
}
