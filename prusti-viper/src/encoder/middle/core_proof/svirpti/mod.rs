use self::procedure_verifier::ProcedureExecutor;
use super::transformations::{
    encoder_context::EncoderContext, symbolic_execution_new::ProgramContext,
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{predicates::OwnedPredicateInfo, snapshots::SnapshotDomainsInfo},
    Encoder,
};
use log::debug;
use rustc_hash::FxHashSet;
use std::collections::BTreeMap;
use vir_crate::low as vir_low;

mod smt;
mod procedure_verifier;

#[derive(Debug)]
pub(super) struct VerificationResult {}

pub(super) fn verify_program(
    encoder: &mut Encoder,
    source_filename: &str,
    program: vir_low::Program,
    non_aliased_memory_block_addresses: FxHashSet<vir_low::Expression>,
    snapshot_domains_info: &SnapshotDomainsInfo,
    owned_predicates_info: BTreeMap<String, OwnedPredicateInfo>,
    extensionality_gas_constant: &vir_low::Expression,
) -> SpannedEncodingResult<VerificationResult> {
    debug!(
        "purify_with_symbolic_execution {} {}",
        source_filename, program.name
    );
    let mut verifier = Verifier::new();
    let result = verifier.execute(
        source_filename,
        program,
        non_aliased_memory_block_addresses,
        snapshot_domains_info,
        owned_predicates_info,
        extensionality_gas_constant,
        encoder,
    )?;
    unimplemented!();
}

struct Verifier {}

impl Verifier {
    pub(crate) fn new() -> Self {
        Self {}
    }

    pub(crate) fn execute(
        &mut self,
        source_filename: &str,
        program: vir_low::Program,
        non_aliased_memory_block_addresses: FxHashSet<vir_low::Expression>,
        snapshot_domains_info: &SnapshotDomainsInfo,
        owned_predicates_info: BTreeMap<String, OwnedPredicateInfo>,
        extensionality_gas_constant: &vir_low::Expression,
        encoder: &mut impl EncoderContext,
    ) -> SpannedEncodingResult<VerificationResult> {
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
        for procedure in program.procedures {
            let mut procedure_executor =
                ProcedureExecutor::new(self, source_filename, &mut program_context)?;
            procedure_executor.load_domains(&program.domains)?;
            procedure_executor.execute_procedure(&procedure)?;
        }
        unimplemented!();
    }
}
