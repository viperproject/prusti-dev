//! This module contains the symbolic execution engine that is used to purify
//! predicates in the Viper program. This module depends on `ErrorManager` and,
//! therefore, has to be in the `prusti-viper` crate.

mod trace_builder;
mod egg;
mod statements;
mod heap;
mod trace;
mod program_context;
pub(super) mod utils;
mod simplifier;
mod consistency_tracker;

use self::program_context::ProgramContext;
use super::encoder_context::EncoderContext;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{predicates::OwnedPredicateInfo, snapshots::SnapshotDomainsInfo},
};
use log::debug;
use prusti_common::config;
use rustc_hash::FxHashSet;
use std::collections::BTreeMap;
use vir_crate::{
    common::{
        expression::{BinaryOperationHelpers, ExpressionIterator, UnaryOperationHelpers},
        graphviz::ToGraphviz,
    },
    low::{self as vir_low},
};

pub(in super::super) fn purify_with_symbolic_execution(
    encoder: &mut impl EncoderContext,
    source_filename: &str,
    program: vir_low::Program,
    non_aliased_memory_block_addresses: FxHashSet<vir_low::Expression>,
    snapshot_domains_info: &SnapshotDomainsInfo,
    owned_predicates_info: BTreeMap<String, OwnedPredicateInfo>,
    extensionality_gas_constant: &vir_low::Expression,
    purification_round: u32,
) -> SpannedEncodingResult<vir_low::Program> {
    debug!(
        "purify_with_symbolic_execution {} {} {}",
        source_filename, program.name, purification_round
    );
    let mut executor = Executor::new(purification_round);
    let program = executor.execute(
        source_filename,
        program,
        non_aliased_memory_block_addresses,
        snapshot_domains_info,
        owned_predicates_info,
        extensionality_gas_constant,
        encoder,
    )?;
    Ok(program)
}

struct Executor {
    /// Which iteration of purification with symbolic execution we are currently
    /// executing?
    ///
    /// 1. The first iteration should purify all stack-allocated variables that
    ///    are non-aliased by default.
    /// 2. The second iteration should purify heap resources that are dependent
    ///    only on stack-allocated variables.
    purification_round: u32,
}

struct ProcedureExecutor<'a, 'c, EC: EncoderContext> {
    executor: &'a mut Executor,
    source_filename: &'a str,
    program_context: &'a mut ProgramContext<'c, EC>,
    continuations: Vec<Continuation>,
    exhale_label_generator_counter: u64,
    /// The execution trace showing in what order the statements were executed.
    execution_trace_builder: trace_builder::ExecutionTraceBuilder<'a>,
    /// The original execution traces.
    original_traces: Vec<trace::Trace>,
    /// Traces in which purifiable predicates were purified.
    final_traces: Vec<trace::Trace>,
    trace_counter: u64,
}

#[derive(Debug)]
pub struct Continuation {
    next_block_label: vir_low::Label,
    parent_block_label: vir_low::Label,
    condition: vir_low::Expression,
}

impl Executor {
    pub(crate) fn new(purification_round: u32) -> Self {
        Self { purification_round }
    }

    pub(crate) fn execute(
        &mut self,
        source_filename: &str,
        mut program: vir_low::Program,
        non_aliased_memory_block_addresses: FxHashSet<vir_low::Expression>,
        snapshot_domains_info: &SnapshotDomainsInfo,
        owned_predicates_info: BTreeMap<String, OwnedPredicateInfo>,
        extensionality_gas_constant: &vir_low::Expression,
        encoder: &mut impl EncoderContext,
    ) -> SpannedEncodingResult<vir_low::Program> {
        let mut program_context = ProgramContext::new(
            &program.domains,
            &program.functions,
            &program.predicates,
            snapshot_domains_info,
            owned_predicates_info,
            &non_aliased_memory_block_addresses,
            extensionality_gas_constant,
            self.purification_round,
            encoder,
        );
        let mut new_procedures = Vec::new();
        for procedure in program.procedures {
            let procedure_name = procedure.name.clone();
            let procedure_executor = ProcedureExecutor::new(
                self,
                source_filename,
                &procedure_name,
                &mut program_context,
            )?;
            procedure_executor.execute_procedure(procedure, &mut new_procedures)?;
        }
        program.procedures = new_procedures;
        Ok(program)
    }
}

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    fn new(
        executor: &'a mut Executor,
        source_filename: &'a str,
        procedure_name: &'a str,
        program_context: &'a mut ProgramContext<'c, EC>,
    ) -> SpannedEncodingResult<Self> {
        let (bool_type, bool_domain_info) = program_context.get_bool_domain_info();
        Ok(Self {
            executor,
            source_filename,
            continuations: Vec::new(),
            exhale_label_generator_counter: 0,
            execution_trace_builder: trace_builder::ExecutionTraceBuilder::new(
                source_filename,
                procedure_name,
                program_context.get_domains(),
                bool_type,
                bool_domain_info,
            )?,
            program_context,
            original_traces: Vec::new(),
            final_traces: Vec::new(),
            trace_counter: 0,
        })
    }

    fn execute_procedure(
        mut self,
        procedure: vir_low::ProcedureDecl,
        new_procedures: &mut Vec<vir_low::ProcedureDecl>,
    ) -> SpannedEncodingResult<()> {
        debug!(
            "Executing procedure: {} round: {}",
            procedure.name, self.executor.purification_round
        );
        // Intern all non-aliased predicates.
        for address in self
            .program_context
            .get_non_aliased_memory_block_addresses()
        {
            assert!(address.is_heap_independent());
            use vir_low::macros::*;
            let address_is_non_aliased = ty!(Bool);
            let address_non_aliased_call = expr! {
                (ComputeAddress::address_is_non_aliased([address.clone()]))
            };
            self.execution_trace_builder
                .current_egraph_state()
                .assume(&address_non_aliased_call)?;
        }
        let mut current_block = procedure.entry.clone();
        loop {
            if self
                .execution_trace_builder
                .current_egraph_state()
                .is_inconsistent()?
            {
                self.finalize_trace()?;
                if let Some(new_current_block) = self.next_continuation(procedure.position)? {
                    current_block = new_current_block;
                    continue;
                } else {
                    break;
                }
            }
            let block = procedure.basic_blocks.get(&current_block).unwrap();
            self.execute_block(&current_block, block)?;
            if self
                .execution_trace_builder
                .current_egraph_state()
                .is_inconsistent()?
            {
                self.finalize_trace()?;
                if let Some(new_current_block) = self.next_continuation(procedure.position)? {
                    current_block = new_current_block;
                    continue;
                } else {
                    break;
                }
            }
            match &block.successor {
                vir_low::Successor::Return => {
                    self.finalize_trace()?;
                    if let Some(new_current_block) = self.next_continuation(procedure.position)? {
                        current_block = new_current_block;
                    } else {
                        break;
                    }
                }
                vir_low::Successor::Goto(label) => current_block = label.clone(),
                vir_low::Successor::GotoSwitch(targets) => {
                    let parent_block_label = current_block.clone();
                    self.execution_trace_builder
                        .add_split_point(parent_block_label.clone())?;
                    // Since the jumps are evaluated one after another, we need
                    // to negate all the previous conditions when considering
                    // the new one.
                    let mut negated_conditions = Vec::new();
                    let mut targets = targets.iter();
                    let (condition, label) = targets.next().unwrap();
                    self.assume_condition(condition.clone(), procedure.position)?;
                    current_block = label.clone();
                    negated_conditions.push(UnaryOperationHelpers::not(condition.clone()));
                    for (condition, label) in targets {
                        let continuation = Continuation {
                            next_block_label: label.clone(),
                            parent_block_label: parent_block_label.clone(),
                            condition: vir_low::Expression::and(
                                negated_conditions.clone().into_iter().conjoin(),
                                condition.clone(),
                            ),
                        };
                        self.continuations.push(continuation);
                        negated_conditions.push(UnaryOperationHelpers::not(condition.clone()));
                    }
                }
            }
        }
        self.finalize_traces()?;
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_symbex_original",
                format!(
                    "{}.{}.round-{}.dot",
                    self.source_filename, procedure.name, self.executor.purification_round,
                ),
                |writer| {
                    self.execution_trace_builder
                        .original_view()
                        .to_graphviz(writer)
                        .unwrap()
                },
            );
            for (i, trace) in self.original_traces.iter().enumerate() {
                prusti_common::report::log::report_with_writer(
                    "vir_symbex_original_traces",
                    format!(
                        "{}.{}.round-{}.{}.vpr",
                        self.source_filename, procedure.name, self.executor.purification_round, i
                    ),
                    |writer| trace.write(writer).unwrap(),
                );
            }
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_symbex_optimized",
                format!(
                    "{}.{}.round-{}.dot",
                    self.source_filename, procedure.name, self.executor.purification_round,
                ),
                |writer| {
                    self.execution_trace_builder
                        .heap_view()
                        .to_graphviz(writer)
                        .unwrap()
                },
            );
            for (i, trace) in self.final_traces.iter().enumerate() {
                prusti_common::report::log::report_with_writer(
                    "vir_symbex_optimized_traces",
                    format!(
                        "{}.{}.round-{}.{}.vpr",
                        self.source_filename, procedure.name, self.executor.purification_round, i
                    ),
                    |writer| trace.write(writer).unwrap(),
                );
            }
        }
        if config::purify_with_symbolic_execution() {
            if config::symbolic_execution_single_method() {
                let new_procedure = self.execution_trace_builder.into_procedure(&procedure);
                prusti_common::report::log::report_with_writer(
                    "graphviz_method_vir_low_symbex_single_method",
                    format!("{}.{}.dot", self.source_filename, new_procedure.name),
                    |writer| new_procedure.to_graphviz(writer).unwrap(),
                );
                new_procedures.push(new_procedure);
            } else {
                for (i, trace) in self.final_traces.into_iter().enumerate() {
                    let new_procedure = trace.into_procedure(i, &procedure);
                    new_procedures.push(new_procedure);
                }
            }
        } else {
            for (i, trace) in self.original_traces.into_iter().enumerate() {
                let new_procedure = trace.into_procedure(i, &procedure);
                new_procedures.push(new_procedure);
            }
        }
        Ok(())
    }

    fn next_continuation(
        &mut self,
        default_position: vir_low::Position,
    ) -> SpannedEncodingResult<Option<vir_low::Label>> {
        while let Some(continuation) = self.continuations.pop() {
            debug!("Rolling back to {}", continuation.parent_block_label);
            self.execution_trace_builder
                .rollback_to_split_point(continuation.parent_block_label)?;
            self.assume_condition(continuation.condition, default_position)?;
            if self
                .execution_trace_builder
                .current_egraph_state()
                .is_inconsistent()?
            {
                debug!("Inconsistent state after rollback");
                self.execution_trace_builder.remove_last_block()?;
            } else {
                return Ok(Some(continuation.next_block_label));
            }
        }
        Ok(None)
    }

    fn assume_condition(
        &mut self,
        condition: vir_low::Expression,
        default_position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        self.execution_trace_builder
            .current_egraph_state()
            .try_assume_heap_independent_conjuncts(&condition)?;
        self.execution_trace_builder
            .heap_assume(condition.clone(), default_position)?;
        self.execution_trace_builder
            .add_original_statement(vir_low::Statement::assume(condition, default_position))?;
        Ok(())
    }

    fn execute_block(
        &mut self,
        current_block: &vir_low::Label,
        block: &vir_low::BasicBlock,
    ) -> SpannedEncodingResult<()> {
        debug!("Executing block {}", current_block);
        let comment = format!("Executing block: {current_block}");
        self.execution_trace_builder
            .add_original_statement(vir_low::Statement::comment(comment.clone()))?;
        self.execution_trace_builder
            .heap_comment(vir_low::Comment::new(comment))?;
        for statement in &block.statements {
            self.execute_statement(current_block, statement)?;
            if self
                .execution_trace_builder
                .current_egraph_state()
                .is_inconsistent()?
            {
                break;
            }
        }
        Ok(())
    }

    fn finalize_trace(&mut self) -> SpannedEncodingResult<()> {
        // // TODO: Instead of finalizing eagerly, collect all leaves and finalize
        // // traces ending at them.
        // self.execution_trace_builder
        //     .current_egraph_state()
        //     .saturate()?;
        // let (original_trace, final_trace) = self
        //     .execution_trace_builder
        //     .finalize_last_trace(self.program_context)?;
        // self.original_traces.push(original_trace);
        // self.final_traces.push(final_trace);
        // This assert safe guards us from crashing the machine by consuming too
        // much memory.
        // self.trace_counter += 1;
        // assert!(self.trace_counter <= 100, "Traces budget exceeded");
        Ok(())
    }

    fn finalize_traces(&mut self) -> SpannedEncodingResult<()> {
        for leaf in self.execution_trace_builder.get_leaves() {
            self.execution_trace_builder
                .get_egraph_state(leaf)
                .saturate()?;
            let (original_trace, final_trace) = self
                .execution_trace_builder
                .finalize_trace(self.program_context, leaf)?;
            self.original_traces.push(original_trace);
            self.final_traces.push(final_trace);
        }
        Ok(())
    }
}
