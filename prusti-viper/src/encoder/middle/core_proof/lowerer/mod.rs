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
    places::PlacesState,
    predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface, PredicatesState},
    snapshots::{SnapshotVariablesInterface, SnapshotsState},
    types::TypesState,
};
use crate::encoder::{errors::SpannedEncodingResult, Encoder};
use rustc_hash::FxHashSet;
use vir_crate::{
    common::{cfg::Cfg, check_mode::CheckMode, graphviz::ToGraphviz},
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
    let result = lowerer.lower_procedure(procedure)?;
    if prusti_common::config::dump_debug_info() {
        let source_filename = encoder.env().source_file_name();
        prusti_common::report::log::report_with_writer(
            "graphviz_method_vir_low",
            format!("{}.{}.dot", source_filename, result.procedure.name),
            |writer| result.procedure.to_graphviz(writer).unwrap(),
        );
    }
    Ok(result)
}

pub(super) struct Lowerer<'p, 'v: 'p, 'tcx: 'v> {
    pub(super) encoder: &'p mut Encoder<'v, 'tcx>,
    pub(super) procedure_name: Option<String>,
    pub(super) check_mode: Option<CheckMode>,
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
    pub(super) places_state: PlacesState,
}

impl<'p, 'v: 'p, 'tcx: 'v> Lowerer<'p, 'v, 'tcx> {
    pub(super) fn new(encoder: &'p mut Encoder<'v, 'tcx>) -> Self {
        Self {
            encoder,
            procedure_name: None,
            check_mode: None,
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
            places_state: Default::default(),
        }
    }

    pub(super) fn lower_procedure(
        mut self,
        mut procedure: vir_mid::ProcedureDecl,
    ) -> SpannedEncodingResult<LoweringResult> {
        let mut basic_blocks_map = BTreeMap::new();
        let mut basic_block_edges = BTreeMap::new();
        let predecessors = procedure.predecessors_owned();
        let traversal_order = procedure.get_topological_sort();
        self.procedure_name = Some(procedure.name.clone());
        self.check_mode = Some(procedure.check_mode);
        let mut marker_initialisation = Vec::new();
        for label in &traversal_order {
            self.set_current_block_for_snapshots(label, &predecessors, &mut basic_block_edges)?;
            let basic_block = procedure.basic_blocks.remove(label).unwrap();
            let marker = self.create_block_marker(label)?;
            marker_initialisation.push(vir_low::Statement::assign_no_pos(
                marker.clone(),
                false.into(),
            ));
            let mut statements = vec![
                vir_low::Statement::assign_no_pos(marker.clone(), true.into()),
                // We need to use a function call here because Silicon optimizes
                // out assignments to pure variables and our Z3 wrapper does not
                // see them.
                vir_low::Statement::log_event(self.create_domain_func_app(
                    "MarkerCalls",
                    format!("basic_block_marker${}", marker.name),
                    vec![],
                    vir_low::Type::Bool,
                    Default::default(),
                )?),
            ];
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
        for basic_block_id in traversal_order {
            let (statements, mut successor) = basic_blocks_map.remove(&basic_block_id).unwrap();
            let label = basic_block_id.clone().into_low(&mut self)?;
            if let Some(intermediate_blocks) = basic_block_edges.remove(&basic_block_id) {
                for (successor_label, successor_statements) in intermediate_blocks {
                    let successor_label = successor_label.into_low(&mut self)?;
                    let intermediate_block_label = vir_low::Label::new(format!(
                        "label__from__{}__to__{}",
                        label.name, successor_label.name
                    ));
                    successor.replace_label(&successor_label, intermediate_block_label.clone());
                    basic_blocks.push(vir_low::BasicBlock {
                        label: intermediate_block_label,
                        statements: successor_statements,
                        successor: vir_low::Successor::Goto(successor_label),
                    });
                }
            }

            basic_blocks.push(vir_low::BasicBlock {
                label,
                statements,
                successor,
            });
        }
        let mut removed_functions = FxHashSet::default();
        if procedure.check_mode == CheckMode::Specifications {
            removed_functions.insert(self.encode_memory_block_bytes_function_name()?);
        }
        let mut predicates = self.collect_owned_predicate_decls()?;
        let mut domains = self.domains_state.destruct();
        domains.extend(self.compute_address_state.destruct());
        predicates.extend(self.predicates_state.destruct());
        let mut lowered_procedure = vir_low::ProcedureDecl {
            name: procedure.name,
            locals: self.variables_state.destruct(),
            basic_blocks,
        };
        let mut methods = self.methods_state.destruct();
        if procedure.check_mode == CheckMode::Specifications {
            super::transformations::remove_predicates::remove_predicates(
                &mut lowered_procedure,
                &mut methods,
                &removed_functions,
            );
        };
        Ok(LoweringResult {
            procedure: lowered_procedure,
            domains,
            functions: self.functions_state.destruct(),
            predicates,
            methods,
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

    pub(super) fn only_check_specs(&self) -> bool {
        self.check_mode.unwrap() == CheckMode::Specifications
    }
}
