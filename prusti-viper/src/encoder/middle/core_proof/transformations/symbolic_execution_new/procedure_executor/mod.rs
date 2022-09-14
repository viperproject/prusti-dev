use self::{heap::GlobalHeapState, state::StateKeeper, variables::VariableVersions};
use super::{
    super::encoder_context::EncoderContext, block_builder::BlockBuilder,
    expression_interner::ExpressionInterner, program_context::ProgramContext,
    trace_builder::TraceBuilder, Executor,
};
use crate::encoder::errors::SpannedEncodingResult;
use log::debug;
use prusti_common::config;

use std::collections::BTreeMap;
use vir_crate::{
    common::{
        cfg::Cfg,
        expression::{BinaryOperationHelpers, ExpressionIterator, SyntacticEvaluation},
        graphviz::ToGraphviz,
    },
    low::{self as vir_low},
};

mod statements;
mod constraints;
mod variables;
mod heap;
mod graphviz;
mod state;
mod block_marker_conditions;
mod expressions;

pub(super) struct ProcedureExecutor<'a, 'c, EC: EncoderContext> {
    executor: &'a mut Executor,
    source_filename: &'a str,
    program_context: &'a mut ProgramContext<'c, EC>,
    procedure: &'a vir_low::ProcedureDecl,
    reaching_predecessors: BTreeMap<vir_low::Label, Vec<vir_low::Label>>,
    current_block: Option<vir_low::Label>,
    current_block_builder: Option<BlockBuilder>,
    trace_builder: TraceBuilder,
    expression_interner: ExpressionInterner,
    // path_constraints: PathConstraints,
    // heap: Heap,
    state_keeper: StateKeeper,
    variable_versions: VariableVersions,
    exhale_label_generator_counter: u64,
    global_heap_state: GlobalHeapState,
    custom_labels: Vec<vir_low::Label>,
    return_blocks: Vec<vir_low::Label>,
}

impl<'a, 'c, EC: EncoderContext> Drop for ProcedureExecutor<'a, 'c, EC> {
    fn drop(&mut self) {
        if prusti_common::config::dump_debug_info() && std::thread::panicking() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_crashing_symbolic_execution",
                format!("{}.{}.crash.dot", self.source_filename, self.procedure.name,),
                |writer| self.to_graphviz(writer).unwrap(),
            );
        }
    }
}

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn new(
        executor: &'a mut Executor,
        source_filename: &'a str,
        program_context: &'a mut ProgramContext<'c, EC>,
        procedure: &'a vir_low::ProcedureDecl,
    ) -> SpannedEncodingResult<Self> {
        Ok(Self {
            executor,
            source_filename,
            program_context,
            procedure,
            reaching_predecessors: Default::default(),
            current_block: None,
            current_block_builder: None,
            trace_builder: TraceBuilder::new()?,
            expression_interner: Default::default(),
            state_keeper: Default::default(),
            // path_constraints: PathConstraints::new(),
            // heap: Heap::new(),
            variable_versions: Default::default(),
            exhale_label_generator_counter: 0,
            global_heap_state: Default::default(),
            custom_labels: Vec::new(),
            return_blocks: Vec::new(),
        })
    }

    pub(super) fn execute_procedure(
        mut self,
        new_procedures: &'a mut Vec<vir_low::ProcedureDecl>,
    ) -> SpannedEncodingResult<()> {
        debug!("Executing procedure: {}", self.procedure.name);
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_before_symbolic_execution",
                format!("{}.{}.dot", self.source_filename, self.procedure.name),
                |writer| self.procedure.to_graphviz(writer).unwrap(),
            );
        }
        self.reaching_predecessors
            .insert(self.procedure.entry.clone(), Vec::new());
        let traversal_order = self.procedure.get_topological_sort();
        for current_block in traversal_order {
            if !self.reaching_predecessors.contains_key(&current_block) {
                // The block is unreachable.
                continue;
            }
            let block = self.procedure.basic_blocks.get(&current_block).unwrap();
            if self.execute_block(&current_block, block)? {
                match &block.successor {
                    vir_low::Successor::Return => {
                        self.return_blocks.push(current_block);
                    }
                    vir_low::Successor::Goto(target) => {
                        self.mark_predecessor_as_analyzed(current_block, target);
                    }
                    vir_low::Successor::GotoSwitch(targets) => {
                        for (_, target) in targets {
                            self.mark_predecessor_as_analyzed(current_block.clone(), target);
                        }
                    }
                }
            }
        }
        let source_filename = self.source_filename;
        if config::symbolic_execution_single_method() {
            let new_procedure = self.into_procedure()?;
            if prusti_common::config::dump_debug_info() {
                prusti_common::report::log::report_with_writer(
                    "graphviz_method_vir_low_after_symbolic_execution",
                    format!("{}.{}.dot", source_filename, new_procedure.name),
                    |writer| new_procedure.to_graphviz(writer).unwrap(),
                );
            }
            new_procedures.push(new_procedure);
        } else {
            let traces = self.into_procedure_per_trace()?;
            if prusti_common::config::dump_debug_info() {
                for (i, trace) in traces.iter().enumerate() {
                    prusti_common::report::log::report_with_writer(
                        "graphviz_method_vir_low_after_symbolic_execution",
                        format!("{}.{}.{}.dot", i, source_filename, trace.name),
                        |writer| trace.to_graphviz(writer).unwrap(),
                    );
                }
            }
            new_procedures.extend(traces);
        }
        Ok(())
    }

    fn mark_predecessor_as_analyzed(
        &mut self,
        current_block: vir_low::Label,
        target: &vir_low::Label,
    ) {
        let predecessors = self
            .reaching_predecessors
            .entry(target.clone())
            .or_default();
        predecessors.push(current_block);
    }

    fn clear_successors(&mut self) -> SpannedEncodingResult<()> {
        self.current_builder_mut().successors.clear();
        Ok(())
    }

    fn execute_block(
        &mut self,
        current_block: &vir_low::Label,
        block: &vir_low::BasicBlock,
    ) -> SpannedEncodingResult<bool> {
        debug!("Executing block {}", current_block);
        self.create_new_current_block(current_block)?;
        let comment = format!("Executing block: {current_block}");
        self.add_comment(comment)?;
        let mut reached_successor = true;
        for statement in &block.statements {
            self.execute_statement(statement)?;
            if self.path_constraints_inconsistent()? {
                self.add_assume(false.into(), self.procedure.position)?;
                self.clear_successors()?;
                reached_successor = false;
                break;
            }
        }
        self.add_current_block_to_trace()?;
        Ok(reached_successor)
    }

    fn create_new_current_block(
        &mut self,
        current_block: &vir_low::Label,
    ) -> SpannedEncodingResult<()> {
        assert!(self.current_block.is_none());
        assert!(self.current_block_builder.is_none());
        let successors = self
            .procedure
            .successors(current_block)
            .into_iter()
            .cloned()
            .collect();
        let builder = BlockBuilder::new(successors)?;
        self.current_block_builder = Some(builder);
        self.current_block = Some(current_block.clone());
        self.initialize_state_for(current_block)?;
        Ok(())
    }

    fn register_label(&mut self, label: vir_low::Label) -> SpannedEncodingResult<()> {
        self.custom_labels.push(label);
        Ok(())
    }

    fn add_current_block_to_trace(&mut self) -> SpannedEncodingResult<()> {
        self.finalize_current_block()?;
        let label = self.current_block.take().unwrap();
        let builder = self.current_block_builder.take().unwrap();
        self.trace_builder.add_block(label, builder)
    }

    fn current_builder_mut(&mut self) -> &mut BlockBuilder {
        self.current_block_builder.as_mut().unwrap()
    }

    fn construct_edge_block(
        source: &vir_low::Label,
        target: &vir_low::Label,
        edge_blocks: &mut BTreeMap<(vir_low::Label, vir_low::Label), Vec<vir_low::Statement>>,
        basic_blocks: &mut BTreeMap<vir_low::Label, vir_low::BasicBlock>,
    ) -> vir_low::Label {
        if let Some(edge_block) = edge_blocks.remove(&(source.clone(), target.clone())) {
            if !edge_block.is_empty() {
                let edge_block_label =
                    vir_low::Label::new(format!("edge_block_{}__{}", source.name, target.name));
                let edge_block =
                    vir_low::BasicBlock::new(edge_block, vir_low::Successor::Goto(target.clone()));
                basic_blocks.insert(edge_block_label.clone(), edge_block);
                return edge_block_label;
            }
        }
        target.clone()
    }

    fn into_procedure(mut self) -> SpannedEncodingResult<vir_low::ProcedureDecl> {
        self.uninitialize()?;
        let mut counter = 0;
        let mut basic_blocks = BTreeMap::new();
        let mut locals = self.procedure.locals.clone();
        for (label, mut block) in std::mem::take(&mut self.trace_builder.blocks) {
            let successor = match block.successors.len() {
                0 => vir_low::Successor::Return,
                1 => vir_low::Successor::Goto(Self::construct_edge_block(
                    &label,
                    &block.successors[0],
                    &mut self.trace_builder.edge_blocks,
                    &mut basic_blocks,
                )),
                _ => {
                    let non_det_variable = vir_low::VariableDecl::new(
                        format!("non_deterministic_jump${counter}"),
                        vir_low::Type::Int,
                    );
                    counter += 1;
                    let mut targets = Vec::new();
                    let mut disjuncts = Vec::new();
                    for (i, successor) in block.successors.into_iter().enumerate() {
                        let condition =
                            vir_low::Expression::equals(non_det_variable.clone().into(), i.into());
                        disjuncts.push(condition.clone());
                        let actual_successor = Self::construct_edge_block(
                            &label,
                            &successor,
                            &mut self.trace_builder.edge_blocks,
                            &mut basic_blocks,
                        );
                        targets.push((condition, actual_successor));
                    }
                    locals.push(non_det_variable);
                    block.statements.push(vir_low::Statement::assume(
                        disjuncts.into_iter().disjoin(),
                        self.procedure.position,
                    ));
                    vir_low::Successor::GotoSwitch(targets)
                }
            };
            let basic_block = vir_low::BasicBlock::new(block.statements, successor);
            basic_blocks.insert(label, basic_block);
        }
        locals.extend(self.variable_versions.create_variable_decls());
        locals.extend(self.global_heap_state.clone_variables());
        let mut custom_labels = self.procedure.custom_labels.clone();
        custom_labels.extend(std::mem::take(&mut self.custom_labels));
        let entry_block = basic_blocks.get_mut(&self.procedure.entry).unwrap();
        let permission_variable_initialization = self
            .global_heap_state
            .initialize_permission_variables(self.procedure.position);
        entry_block
            .statements
            .splice(0..0, permission_variable_initialization);
        let procedure = vir_low::ProcedureDecl::new(
            self.procedure.name.clone(),
            locals,
            custom_labels,
            self.procedure.entry.clone(),
            self.procedure.exit.clone(),
            basic_blocks,
        );
        Ok(procedure)
    }

    fn into_procedure_per_trace(mut self) -> SpannedEncodingResult<Vec<vir_low::ProcedureDecl>> {
        self.uninitialize()?;
        fn dfs(
            builder: &TraceBuilder,
            current_block: &vir_low::Label,
            trace: &mut Vec<vir_low::Label>,
            traces: &mut Vec<Vec<vir_low::Label>>,
        ) {
            trace.push(current_block.clone());
            // Check if we have assume false and terminate if we do.
            for statement in &builder.blocks[current_block].statements {
                if let vir_low::Statement::Assume(statement) = statement {
                    if statement.expression.is_false() {
                        traces.push(trace.clone());
                        trace.pop();
                        return;
                    }
                }
            }
            let successors = &builder.blocks[current_block].successors;
            if successors.is_empty() {
                traces.push(trace.clone());
            } else {
                for successor in successors {
                    dfs(builder, successor, trace, traces);
                }
            }
            trace.pop();
        }
        let mut traces = Vec::new();
        let mut trace = vec![];
        dfs(
            &self.trace_builder,
            &self.procedure.entry,
            &mut trace,
            &mut traces,
        );
        let mut procedures = Vec::new();
        for (i, trace) in traces.into_iter().enumerate() {
            let mut basic_blocks = BTreeMap::new();
            let mut statements = Vec::new();
            for (i, label) in trace.iter().enumerate() {
                let block = &self.trace_builder.blocks[label];
                statements.extend(block.statements.clone());
                if let Some(next_label) = trace.get(i + 1) {
                    if let Some(edge_block) = self
                        .trace_builder
                        .edge_blocks
                        .get(&(label.clone(), next_label.clone()))
                    {
                        statements.extend(edge_block.clone());
                    }
                }
            }
            basic_blocks.insert(
                self.procedure.entry.clone(),
                vir_low::BasicBlock::new(statements, vir_low::Successor::Return),
            );
            let mut locals = self.procedure.locals.clone();
            locals.extend(self.variable_versions.create_variable_decls());
            locals.extend(self.global_heap_state.clone_variables());
            let mut custom_labels = self.procedure.custom_labels.clone();
            custom_labels.extend(self.custom_labels.clone());
            let entry_block = basic_blocks.get_mut(&self.procedure.entry).unwrap();
            let permission_variable_initialization = self
                .global_heap_state
                .initialize_permission_variables(self.procedure.position);
            entry_block
                .statements
                .splice(0..0, permission_variable_initialization);
            let procedure = vir_low::ProcedureDecl::new(
                format!("{}$trace{}", self.procedure.name, i),
                locals,
                custom_labels,
                self.procedure.entry.clone(),
                self.procedure.exit.clone(),
                basic_blocks,
            );
            procedures.push(procedure);
        }
        Ok(procedures)
    }

    fn uninitialize(&mut self) -> SpannedEncodingResult<()> {
        assert!(self.current_block.is_none());
        assert!(self.current_block_builder.is_none());
        // self.heap.uninitialize(&self.return_blocks)?;
        // self.path_constraints.uninitialize()?;
        self.state_keeper.uninitialize(&self.return_blocks)?;
        Ok(())
    }
}
