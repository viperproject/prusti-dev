use self::{
    domains::DomainsLowererState, functions::FunctionsLowererState, methods::MethodsLowererState,
    predicates::PredicatesLowererState, variables::VariablesLowererState,
};
use super::{
    builtin_methods::BuiltinMethodsState,
    compute_address::ComputeAddressState,
    into_low::IntoLow,
    predicates_memory_block::PredicatesMemoryBlockState,
    predicates_owned::{PredicatesOwnedInterface, PredicatesOwnedState},
    snapshots::SnapshotsState,
};
use crate::encoder::{errors::SpannedEncodingResult, Encoder};

use vir_crate::{
    low::{self as vir_low, operations::ty::Typed},
    middle as vir_mid,
};

mod domains;
mod functions;
mod methods;
mod predicates;
mod variables;

pub(super) use self::{
    domains::DomainsLowererInterface, functions::FunctionsLowererInterface,
    methods::MethodsLowererInterface, predicates::PredicatesLowererInterface,
    variables::VariablesLowererInterface,
};

pub(super) struct LoweringResult {
    pub(super) procedure: vir_low::ProcedureDecl,
    pub(super) domains: Vec<vir_low::DomainDecl>,
    pub(super) functions: Vec<vir_low::FunctionDecl>,
    pub(super) predicates: Vec<vir_low::PredicateDecl>,
    pub(super) methods: Vec<vir_low::MethodDecl>,
}

pub(super) fn lower_procedure<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p mut Encoder<'v, 'tcx>,
    procedure: vir_mid::ProcedureDecl,
) -> SpannedEncodingResult<LoweringResult> {
    let lowerer = self::Lowerer::new(encoder);
    lowerer.lower_procedure(procedure)
}

pub(super) struct Lowerer<'p, 'v: 'p, 'tcx: 'v> {
    pub(super) encoder: &'p mut Encoder<'v, 'tcx>,
    pub(super) procedure_name: Option<String>,
    variables_state: VariablesLowererState,
    functions_state: FunctionsLowererState,
    domains_state: DomainsLowererState,
    predicates_state: PredicatesLowererState,
    methods_state: MethodsLowererState,
    pub(super) predicates_memory_block_state: PredicatesMemoryBlockState,
    pub(super) predicates_owned_state: PredicatesOwnedState,
    pub(super) builtin_methods_state: BuiltinMethodsState,
    pub(super) compute_address_state: ComputeAddressState,
    pub(super) snapshots_state: SnapshotsState,
}

impl<'p, 'v: 'p, 'tcx: 'v> Lowerer<'p, 'v, 'tcx> {
    pub(super) fn new(encoder: &'p mut Encoder<'v, 'tcx>) -> Self {
        Self {
            encoder,
            procedure_name: None,
            variables_state: Default::default(),
            functions_state: Default::default(),
            domains_state: Default::default(),
            predicates_state: Default::default(),
            methods_state: Default::default(),
            predicates_memory_block_state: Default::default(),
            builtin_methods_state: Default::default(),
            compute_address_state: Default::default(),
            snapshots_state: Default::default(),
            predicates_owned_state: Default::default(),
        }
    }
    pub(super) fn lower_procedure(
        mut self,
        mut procedure: vir_mid::ProcedureDecl,
    ) -> SpannedEncodingResult<LoweringResult> {
        self.collect_existing_variables(&procedure)?;
        let mut basic_blocks = Vec::new();
        let traversal_order = procedure.get_topological_sort();
        self.procedure_name = Some(procedure.name.clone());
        for label in traversal_order {
            let basic_block = procedure.basic_blocks.remove(&label).unwrap();
            let mut statements = Vec::new();
            for statement in basic_block.statements {
                statements.extend(statement.into_low(&mut self)?);
            }
            let block = vir_low::BasicBlock {
                label: label.into_low(&mut self)?,
                statements,
                successor: basic_block.successor.into_low(&mut self)?,
            };
            basic_blocks.push(block);
        }
        let mut predicates = self.collect_owned_predicate_decls()?;
        let mut domains = self.domains_state.destruct();
        domains.extend(self.compute_address_state.destruct());
        predicates.extend(self.predicates_state.destruct());
        let lowered_procedure = vir_low::ProcedureDecl {
            name: procedure.name,
            locals: self.variables_state.destruct(),
            basic_blocks,
        };
        Ok(LoweringResult {
            procedure: lowered_procedure,
            domains,
            functions: self.functions_state.destruct(),
            predicates,
            methods: self.methods_state.destruct(),
        })
    }
    fn create_parameters(&self, arguments: &[vir_low::Expression]) -> Vec<vir_low::VariableDecl> {
        arguments
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                vir_low::VariableDecl::new(format!("_{}", index), arg.get_type().clone())
            })
            .collect()
    }
}
