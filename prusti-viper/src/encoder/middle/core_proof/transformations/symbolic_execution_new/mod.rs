//! This module contains the symbolic execution engine that is used to purify
//! predicates in the Viper program. This module depends on `ErrorManager` and,
//! therefore, has to be in the `prusti-viper` crate.

use self::{procedure_executor::ProcedureExecutor, program_context::ProgramContext};
use super::encoder_context::EncoderContext;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{predicates::OwnedPredicateInfo, snapshots::SnapshotDomainsInfo},
};
use log::debug;

use rustc_hash::FxHashSet;
use std::collections::BTreeMap;
use vir_crate::low::{self as vir_low};

mod program_context;
mod procedure_executor;
mod block_builder;
mod trace_builder;
mod expression_interner;
mod egg;

pub(in super::super) fn purify_with_symbolic_execution(
    encoder: &mut impl EncoderContext,
    source_filename: &str,
    program: vir_low::Program,
    non_aliased_memory_block_addresses: FxHashSet<vir_low::Expression>,
    snapshot_domains_info: &SnapshotDomainsInfo,
    owned_predicates_info: BTreeMap<String, OwnedPredicateInfo>,
    extensionality_gas_constant: &vir_low::Expression,
) -> SpannedEncodingResult<vir_low::Program> {
    debug!(
        "purify_with_symbolic_execution {} {}",
        source_filename, program.name
    );
    let mut executor = Executor::new();
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

struct Executor {}

impl Executor {
    pub(crate) fn new() -> Self {
        Self {}
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
            encoder,
        );
        let mut new_procedures = Vec::new();
        for procedure in program.procedures {
            let procedure_executor =
                ProcedureExecutor::new(self, source_filename, &mut program_context, &procedure)?;
            procedure_executor.execute_procedure(&mut new_procedures)?;
        }
        program.procedures = new_procedures;
        Ok(program)
    }
}
