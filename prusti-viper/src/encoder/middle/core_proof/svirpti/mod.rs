use self::procedure_verifier::ProcedureExecutor;
use super::transformations::{
    encoder_context::EncoderContext, predicate_domains::PredicateDomainsInfo,
    symbolic_execution_new::ProgramContext,
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
mod errors;

pub(crate) use self::errors::VerificationError;

#[derive(Debug)]
pub(crate) enum VerificationResult {
    Success,
    Failure { errors: Vec<VerificationError> },
}

impl VerificationResult {
    pub(crate) fn is_success(&self) -> bool {
        matches!(self, Self::Success)
    }

    pub(crate) fn get_errors(&self) -> &[VerificationError] {
        match self {
            Self::Success => &[],
            Self::Failure { errors } => errors,
        }
    }
}

pub(super) fn verify_program(
    encoder: &mut Encoder,
    source_filename: &str,
    program: vir_low::Program,
    predicate_domains_info: PredicateDomainsInfo,
    non_aliased_memory_block_addresses: FxHashSet<vir_low::Expression>,
    snapshot_domains_info: &SnapshotDomainsInfo,
    owned_predicates_info: BTreeMap<String, OwnedPredicateInfo>,
    extensionality_gas_constant: &vir_low::Expression,
) -> SpannedEncodingResult<VerificationResult> {
    debug!(
        "purify_with_symbolic_execution {} {}",
        source_filename, program.name
    );
    let mut verifier = Verifier::new(program.name.clone());
    verifier.execute(
        source_filename,
        program,
        predicate_domains_info,
        non_aliased_memory_block_addresses,
        snapshot_domains_info,
        owned_predicates_info,
        extensionality_gas_constant,
        encoder,
    )?;
    let result = if verifier.errors.is_empty() {
        VerificationResult::Success
    } else {
        VerificationResult::Failure {
            errors: verifier.errors,
        }
    };
    Ok(result)
}

struct Verifier {
    program_name: String,
    errors: Vec<VerificationError>,
}

impl Verifier {
    pub(crate) fn new(program_name: String) -> Self {
        Self {
            program_name,
            errors: Vec::new(),
        }
    }

    pub(crate) fn execute(
        &mut self,
        source_filename: &str,
        program: vir_low::Program,
        predicate_domains_info: PredicateDomainsInfo,
        non_aliased_memory_block_addresses: FxHashSet<vir_low::Expression>,
        snapshot_domains_info: &SnapshotDomainsInfo,
        owned_predicates_info: BTreeMap<String, OwnedPredicateInfo>,
        extensionality_gas_constant: &vir_low::Expression,
        encoder: &mut impl EncoderContext,
    ) -> SpannedEncodingResult<()> {
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
            let mut procedure_executor = ProcedureExecutor::new(
                self,
                source_filename,
                procedure.name.clone(),
                &mut program_context,
                &predicate_domains_info,
            )?;
            procedure_executor.load_domains(&program.domains)?;
            procedure_executor.execute_procedure(&procedure, &program.predicates)?;
        }
        Ok(())
    }

    pub(crate) fn report_error(&mut self, error: VerificationError) {
        self.errors.push(error);
    }
}
