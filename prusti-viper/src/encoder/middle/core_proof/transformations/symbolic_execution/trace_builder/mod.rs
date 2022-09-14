mod original_view;
mod heap_view;

use super::{
    egg::EGraphState,
    heap::{HeapEntry, HeapState},
    program_context::ProgramContext,
    trace::Trace,
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        snapshots::SnapshotDomainInfo, transformations::encoder_context::EncoderContext,
    },
};
use rustc_hash::FxHashMap;
use std::collections::BTreeMap;
use vir_crate::{
    common::{expression::BinaryOperationHelpers, graphviz::ToGraphviz},
    low::{self as vir_low},
};

pub(super) use self::{
    heap_view::ExecutionTraceHeapView, original_view::ExecutionTraceOriginalView,
};

pub(super) struct ExecutionTraceBuilder<'a> {
    pub(super) source_filename: &'a str,
    pub(super) procedure_name: &'a str,
    blocks: Vec<ExecutionTraceBlock>,
    split_point_parents: BTreeMap<vir_low::Label, usize>,
    variable_versions: FxHashMap<String, u64>,
}

impl<'a> Drop for ExecutionTraceBuilder<'a> {
    fn drop(&mut self) {
        if prusti_common::config::dump_debug_info() && std::thread::panicking() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_symbex_original",
                format!("{}.{}.crash.dot", self.source_filename, self.procedure_name,),
                |writer| self.original_view().to_graphviz(writer).unwrap(),
            );
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_symbex_optimized",
                format!("{}.{}.crash.dot", self.source_filename, self.procedure_name,),
                |writer| self.heap_view().to_graphviz(writer).unwrap(),
            );
            let mut original_trace = Trace {
                statements: Vec::new(),
                variables: Vec::new(),
                labels: Vec::new(),
            };
            self.finalize_original_trace_for_block(&mut original_trace, self.blocks.len() - 1)
                .unwrap();
            prusti_common::report::log::report_with_writer(
                "vir_symbex_original_traces",
                format!("{}.{}.crash.vpr", self.source_filename, self.procedure_name),
                |writer| original_trace.write(writer).unwrap(),
            );
        }
    }
}

impl<'a> ExecutionTraceBuilder<'a> {
    pub(super) fn new(
        source_filename: &'a str,
        procedure_name: &'a str,
        domains: &[vir_low::DomainDecl],
        bool_type: vir_low::Type,
        bool_domain_info: SnapshotDomainInfo,
    ) -> SpannedEncodingResult<Self> {
        let initial_block = ExecutionTraceBlock::root(domains, bool_type, bool_domain_info)?;
        Ok(Self {
            source_filename,
            procedure_name,
            blocks: vec![initial_block],
            split_point_parents: Default::default(),
            variable_versions: Default::default(),
        })
    }

    fn current_block(&self) -> &ExecutionTraceBlock {
        self.blocks.last().unwrap()
    }

    fn current_block_mut(&mut self) -> &mut ExecutionTraceBlock {
        self.blocks.last_mut().unwrap()
    }

    pub(super) fn current_egraph_state(&mut self) -> &mut EGraphState {
        self.current_block_mut().egraph_state.as_mut().unwrap()
    }

    pub(super) fn get_egraph_state(&mut self, block_id: usize) -> &mut EGraphState {
        self.blocks[block_id].egraph_state.as_mut().unwrap()
    }

    pub(super) fn current_heap_state_mut(&mut self) -> &mut HeapState {
        &mut self.current_block_mut().heap_state
    }

    pub(super) fn current_heap_state(&self) -> &HeapState {
        &self.current_block().heap_state
    }

    pub(super) fn heap_state(&self, block_id: usize) -> &HeapState {
        &self.blocks[block_id].heap_state
    }

    pub(super) fn steal_current_egraph_solver(&mut self) -> EGraphState {
        std::mem::take(&mut self.current_block_mut().egraph_state).unwrap()
    }

    pub(super) fn steal_egraph_solver(&mut self, block_id: usize) -> EGraphState {
        std::mem::take(&mut self.blocks[block_id].egraph_state).unwrap()
    }

    pub(super) fn current_heap_and_egraph_state(&self) -> (&HeapState, &EGraphState) {
        let current_block = self.current_block();
        (
            &current_block.heap_state,
            (current_block.egraph_state.as_ref().unwrap()),
        )
    }

    pub(super) fn current_heap_and_egraph_state_mut(
        &mut self,
    ) -> (&mut HeapState, &mut EGraphState) {
        let current_block = self.current_block_mut();
        (
            &mut current_block.heap_state,
            current_block.egraph_state.as_mut().unwrap(),
        )
    }

    pub(super) fn add_original_statement(
        &mut self,
        statement: vir_low::Statement,
    ) -> SpannedEncodingResult<()> {
        let current_block = self.current_block_mut();
        current_block.original_statements.push(statement);
        Ok(())
    }

    pub(super) fn add_heap_entry(&mut self, entry: HeapEntry) -> SpannedEncodingResult<()> {
        let current_block = self.current_block_mut();
        current_block.heap_statements.push(entry);
        Ok(())
    }

    pub(super) fn add_split_point(
        &mut self,
        parent_block_label: vir_low::Label,
    ) -> SpannedEncodingResult<()> {
        let parent_id = self.blocks.len() - 1;
        let new_block = ExecutionTraceBlock::from_parent(parent_id, self.current_block());
        self.blocks.push(new_block);
        self.split_point_parents
            .insert(parent_block_label, parent_id);
        Ok(())
    }

    pub(super) fn rollback_to_split_point(
        &mut self,
        split_point_label: vir_low::Label,
    ) -> SpannedEncodingResult<()> {
        let parent_id = self.split_point_parents[&split_point_label];
        let parent = &self.blocks[parent_id];
        let new_block = ExecutionTraceBlock::from_parent(parent_id, parent);
        self.blocks.push(new_block);
        Ok(())
    }

    pub(super) fn original_view(&self) -> ExecutionTraceOriginalView {
        ExecutionTraceOriginalView { trace: self }
    }

    pub(super) fn heap_view(&self) -> ExecutionTraceHeapView {
        ExecutionTraceHeapView { trace: self }
    }

    pub(super) fn create_new_bool_variable_version(
        &mut self,
        variable_name: &str,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let version = self
            .variable_versions
            .entry(variable_name.to_string())
            .or_default();
        *version += 1;
        let version = *version;
        let variable =
            vir_low::VariableDecl::new(format!("{variable_name}${version}"), vir_low::Type::Bool);
        self.current_block_mut()
            .new_variables
            .push(variable.clone());
        Ok(variable)
    }

    pub(super) fn register_label(&mut self, label: vir_low::Label) -> SpannedEncodingResult<()> {
        self.current_block_mut().new_labels.push(label);
        Ok(())
    }

    pub(super) fn finalize_last_trace(
        &mut self,
        program: &ProgramContext<impl EncoderContext>,
    ) -> SpannedEncodingResult<(Trace, Trace)> {
        self.finalize_trace(program, self.blocks.len() - 1)
    }

    pub(super) fn finalize_trace(
        &mut self,
        program: &ProgramContext<impl EncoderContext>,
        block_id: usize,
    ) -> SpannedEncodingResult<(Trace, Trace)> {
        let mut original_trace = Trace {
            statements: Vec::new(),
            variables: Vec::new(),
            labels: Vec::new(),
        };
        self.finalize_original_trace_for_block(&mut original_trace, block_id)?;
        let final_trace = self.heap_finalize_trace(program, block_id)?;
        Ok((original_trace, final_trace))
    }

    fn finalize_original_trace_for_block(
        &self,
        trace: &mut Trace,
        block_id: usize,
    ) -> SpannedEncodingResult<()> {
        let block = &self.blocks[block_id];
        if let Some(parent_id) = block.parent {
            self.finalize_original_trace_for_block(trace, parent_id)?;
        }
        for statement in &block.original_statements {
            trace.statements.push(statement.clone());
        }
        Ok(())
    }

    /// Removes the last block from the trace. This method should be used only
    /// when the last method is a freshly added unreachable branch.
    pub(super) fn remove_last_block(&mut self) -> SpannedEncodingResult<()> {
        let last_block = self.blocks.pop().unwrap();
        assert_eq!(last_block.original_statements.len(), 1);
        assert_eq!(last_block.heap_statements.len(), 1);
        Ok(())
    }

    pub(super) fn into_procedure(
        mut self,
        original_procedure: &vir_low::ProcedureDecl,
    ) -> vir_low::ProcedureDecl {
        let entry = vir_low::Label::new("trace_start");
        let exit = vir_low::Label::new("trace_end");
        let mut jump_targets = vec![Vec::new(); self.blocks.len()];
        for (i, block) in self.blocks.iter().enumerate() {
            if let Some(parent) = block.parent {
                jump_targets[parent].push(i);
            }
        }
        let locals = original_procedure.locals.clone();
        let custom_labels = original_procedure.custom_labels.clone();
        let mut basic_blocks = BTreeMap::new();
        for (i, block) in std::mem::take(&mut self.blocks).into_iter().enumerate() {
            let mut statements = block.finalized_statements.borrow_mut().take().unwrap();
            let successor = match jump_targets[i].len() {
                0 => vir_low::Successor::Goto(exit.clone()),
                1 => vir_low::Successor::Goto(vir_low::Label::new(format!(
                    "trace_block_{}",
                    jump_targets[i][0]
                ))),
                _ => {
                    let mut targets = Vec::new();
                    let variable = vir_low::VariableDecl::new(
                        format!("trace_block_{}_guard", i),
                        vir_low::Type::Int,
                    );
                    for (j, target) in jump_targets[i].iter().enumerate() {
                        let guard = vir_low::Expression::equals(variable.clone().into(), j.into());
                        let label = vir_low::Label::new(format!("trace_block_{}", target));
                        targets.push((guard, label));
                    }
                    statements.push(vir_low::Statement::assume(
                        vir_low::Expression::and(
                            vir_low::Expression::greater_equals(0.into(), variable.clone().into()),
                            vir_low::Expression::less_than(
                                variable.into(),
                                jump_targets[i].len().into(),
                            ),
                        ),
                        original_procedure.position,
                    ));
                    vir_low::Successor::GotoSwitch(targets)
                }
            };
            let basic_block = vir_low::BasicBlock::new(statements, successor);
            basic_blocks.insert(
                vir_low::Label::new(format!("trace_block_{}", i)),
                basic_block,
            );
        }
        vir_low::ProcedureDecl::new_with_pos(
            format!("{}$trace", original_procedure.name),
            locals,
            custom_labels,
            entry,
            exit,
            basic_blocks,
            original_procedure.position,
        )
    }

    pub(super) fn get_leaves(&self) -> Vec<usize> {
        let mut has_parent = vec![false; self.blocks.len()];
        let mut is_empty = vec![false; self.blocks.len()];
        for (i, block) in self.blocks.iter().enumerate() {
            if let Some(parent) = block.parent {
                has_parent[parent] = true;
            }
            if block.original_statements.is_empty() {
                is_empty[i] = true;
            } else if block.original_statements.len() == 1 {
                if let vir_low::Statement::Assume(statement) = &block.original_statements[0] {
                    if statement.expression.is_heap_independent() {
                        is_empty[i] = true;
                    }
                }
            }
        }
        let mut is_leaf = vec![true; self.blocks.len()];
        for (i, block) in self.blocks.iter().enumerate() {
            if is_empty[i] && !has_parent[i] {
                // We do not count as a child unless we also have a child.
                continue;
            }
            if let Some(parent) = block.parent {
                is_leaf[parent] = false;
            }
        }
        let mut leaves = Vec::new();
        for (i, is_leaf) in is_leaf.into_iter().enumerate() {
            if is_leaf {
                leaves.push(i);
            }
        }
        leaves
    }
}

struct ExecutionTraceBlock {
    /// The parent of this block. The root does not have a parent.
    parent: Option<usize>,
    /// New variables declared while executing the trace.
    new_variables: Vec<vir_low::VariableDecl>,
    /// New labels declared while executing the trace.
    new_labels: Vec<vir_low::Label>,
    /// Original statements that were executed in the trace.
    original_statements: Vec<vir_low::Statement>,
    /// Statements that make the heap operations more explicit.
    heap_statements: Vec<HeapEntry>,
    /// Statements after all the transformations.
    finalized_statements: std::cell::RefCell<Option<Vec<vir_low::Statement>>>,
    /// The last heap state. If the block is fully executed, it is the state
    /// after the last statement.
    heap_state: HeapState,
    /// The last e-graph state. If the block is fully executed, it is the state
    /// after the last statement.
    egraph_state: Option<EGraphState>,
}

impl ExecutionTraceBlock {
    fn root(
        domains: &[vir_low::DomainDecl],
        bool_type: vir_low::Type,
        bool_domain_info: SnapshotDomainInfo,
    ) -> SpannedEncodingResult<Self> {
        Ok(Self {
            parent: None,
            new_variables: Vec::new(),
            new_labels: Vec::new(),
            original_statements: Vec::new(),
            heap_statements: Vec::new(),
            finalized_statements: std::cell::RefCell::new(None),
            heap_state: HeapState::default(),
            egraph_state: Some(EGraphState::new(domains, bool_type, bool_domain_info)?),
        })
    }

    fn from_parent(parent_id: usize, parent: &Self) -> Self {
        Self {
            parent: Some(parent_id),
            new_variables: Vec::new(),
            new_labels: Vec::new(),
            original_statements: Vec::new(),
            heap_statements: Vec::new(),
            finalized_statements: std::cell::RefCell::new(None),
            heap_state: parent.heap_state.clone(),
            egraph_state: parent.egraph_state.clone(),
        }
    }
}
