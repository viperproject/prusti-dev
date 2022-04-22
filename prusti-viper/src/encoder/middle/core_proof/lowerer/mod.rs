use std::collections::BTreeMap;

use self::{
    domains::DomainsLowererState, functions::FunctionsLowererState, methods::MethodsLowererState,
    predicates::PredicatesLowererState, variables::VariablesLowererState,
};
use super::{
    adts::AdtsState,
    builtin_methods::BuiltinMethodsState,
    compute_address::ComputeAddressState,
    into_low::IntoLow,
    lifetimes::LifetimesState,
    predicates::{PredicatesOwnedInterface, PredicatesState},
    snapshots::{SnapshotVariablesInterface, SnapshotsState},
    types::TypesState,
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
    pub(super) predicates_encoding_state: PredicatesState,
    pub(super) builtin_methods_state: BuiltinMethodsState,
    pub(super) compute_address_state: ComputeAddressState,
    pub(super) snapshots_state: SnapshotsState,
    pub(super) types_state: TypesState,
    pub(super) adts_state: AdtsState,
    pub(super) lifetimes_state: LifetimesState,
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
            predicates_encoding_state: Default::default(),
            builtin_methods_state: Default::default(),
            compute_address_state: Default::default(),
            snapshots_state: Default::default(),
            types_state: Default::default(),
            adts_state: Default::default(),
            lifetimes_state: Default::default(),
        }
    }
    pub(super) fn lower_procedure(
        mut self,
        mut procedure: vir_mid::ProcedureDecl,
    ) -> SpannedEncodingResult<LoweringResult> {
        let mut basic_blocks_map = BTreeMap::new();
        let predecessors = procedure.get_predecessors();
        let traversal_order = procedure.get_topological_sort();
        self.procedure_name = Some(procedure.name.clone());
        let mut marker_initialisation = Vec::new();
        for label in &traversal_order {
            self.set_current_block_for_snapshots(label, &predecessors, &mut basic_blocks_map)?;
            let basic_block = procedure.basic_blocks.remove(label).unwrap();
            let marker = self.create_block_marker(label)?;
            marker_initialisation.push(vir_low::Statement::assign_no_pos(
                marker.clone(),
                false.into(),
            ));
            let mut statements = vec![vir_low::Statement::assign_no_pos(marker, true.into())];
            for statement in basic_block.statements {
                statements.extend(statement.into_low(&mut self)?);
            }
            let successor = basic_block.successor.into_low(&mut self)?;
            basic_blocks_map.insert(label.clone(), (statements, successor));
            self.unset_current_block_for_snapshots(label.clone())?;
        }
        let (entry_block_statements, _) = basic_blocks_map.get_mut(&procedure.entry).unwrap();
        std::mem::swap(entry_block_statements, &mut marker_initialisation);
        entry_block_statements.extend(marker_initialisation);

        let mut basic_blocks = Vec::new();
        for label in traversal_order {
            let (statements, successor) = basic_blocks_map.remove(&label).unwrap();
            let label = label.into_low(&mut self)?;
            basic_blocks.push(vir_low::BasicBlock {
                label,
                statements,
                successor,
            });
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

    fn create_block_marker(
        &mut self,
        label: &vir_mid::BasicBlockId,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        self.create_variable(format!("{}$marker", label), vir_low::Type::Bool)
    }
}
