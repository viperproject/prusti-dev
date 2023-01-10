use self::{
    domains::DomainsLowererState, functions::FunctionsLowererState, methods::MethodsLowererState,
    predicates::PredicatesLowererState, variables::VariablesLowererState,
};
use super::{
    addresses::AddressState,
    adts::AdtsState,
    builtin_methods::BuiltinMethodsState,
    compute_address::ComputeAddressState,
    heap::HeapState,
    into_low::IntoLow,
    labels::LabelsState,
    lifetimes::LifetimesState,
    places::PlacesState,
    predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface, PredicatesState},
    snapshots::{SnapshotVariablesInterface, SnapshotsState},
    types::TypesState,
};
use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    middle::core_proof::builtin_methods::BuiltinMethodsInterface,
    mir::errors::ErrorInterface,
    Encoder,
};
use prusti_rustc_interface::hir::def_id::DefId;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::{BTreeMap, BTreeSet};
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
    pub(super) procedures: Vec<vir_low::ProcedureDecl>,
    pub(super) domains: Vec<vir_low::DomainDecl>,
    pub(super) functions: Vec<vir_low::FunctionDecl>,
    pub(super) predicates: Vec<vir_low::PredicateDecl>,
    pub(super) methods: Vec<vir_low::MethodDecl>,
}

pub(super) fn lower_procedure<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p mut Encoder<'v, 'tcx>,
    def_id: DefId,
    procedure: vir_mid::ProcedureDecl,
) -> SpannedEncodingResult<LoweringResult> {
    let lowerer = self::Lowerer::new(encoder);
    let mut result = lowerer.lower_procedure(def_id, procedure)?;
    if let Some(path) = prusti_common::config::execute_only_failing_trace() {
        let label_markers: FxHashMap<String, bool> =
            serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap();
        super::transformations::remove_unvisited_blocks::remove_unvisited_blocks(
            &mut result.procedures,
            &label_markers,
        )?;
    }
    if prusti_common::config::dump_debug_info() {
        let source_filename = encoder.env().name.source_file_name();
        for procedure in &result.procedures {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| procedure.to_graphviz(writer).unwrap(),
            );
        }
    }
    Ok(result)
}

pub(super) fn lower_type<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p mut Encoder<'v, 'tcx>,
    def_id: Option<DefId>,
    ty: vir_mid::Type,
    check_copy: bool,
) -> SpannedEncodingResult<LoweringResult> {
    let lowerer = self::Lowerer::new(encoder);
    let result = lowerer.lower_type(def_id, ty, check_copy)?;
    Ok(result)
}

pub(super) struct Lowerer<'p, 'v: 'p, 'tcx: 'v> {
    pub(super) encoder: &'p mut Encoder<'v, 'tcx>,
    pub(super) def_id: Option<DefId>,
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
    pub(super) heap_state: HeapState,
    pub(super) address_state: AddressState,
    pub(super) labels_state: LabelsState,
}

impl<'p, 'v: 'p, 'tcx: 'v> Lowerer<'p, 'v, 'tcx> {
    pub(super) fn new(encoder: &'p mut Encoder<'v, 'tcx>) -> Self {
        Self {
            encoder,
            def_id: None,
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
            heap_state: Default::default(),
            address_state: Default::default(),
            labels_state: Default::default(),
        }
    }

    pub(super) fn lower_procedure(
        mut self,
        def_id: DefId,
        mut procedure: vir_mid::ProcedureDecl,
    ) -> SpannedEncodingResult<LoweringResult> {
        self.def_id = Some(def_id);
        let mut basic_blocks_map = BTreeMap::new();
        let mut basic_block_edges = BTreeMap::new();
        let predecessors = procedure.predecessors_owned();
        let traversal_order = procedure.get_topological_sort();
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

        let mut basic_blocks = BTreeMap::new();
        for basic_block_id in traversal_order {
            let (statements, mut successor) = basic_blocks_map.remove(&basic_block_id).unwrap();
            let label = basic_block_id.clone().into_low(&mut self)?;
            if let Some(intermediate_blocks) = basic_block_edges.remove(&basic_block_id) {
                for (successor_label, equalities) in intermediate_blocks {
                    let successor_label = successor_label.into_low(&mut self)?;
                    let intermediate_block_label = vir_low::Label::new(format!(
                        "label__from__{}__to__{}",
                        label.name, successor_label.name
                    ));
                    successor.replace_label(&successor_label, intermediate_block_label.clone());
                    let mut successor_statements = Vec::new();
                    for (variable_name, ty, position, old_version, new_version) in equalities {
                        let new_variable = self.create_snapshot_variable_low(
                            &variable_name,
                            ty.clone(),
                            new_version,
                        )?;
                        let old_variable = self.create_snapshot_variable_low(
                            &variable_name,
                            ty.clone(),
                            old_version,
                        )?;
                        let position = self.encoder.change_error_context(
                            // FIXME: Get a more precise span.
                            position,
                            ErrorCtxt::Unexpected,
                        );
                        let statement = vir_low::macros::stmtp! {
                            position => assume (new_variable == old_variable)
                        };
                        successor_statements.push(statement);
                    }
                    basic_blocks.insert(
                        intermediate_block_label,
                        vir_low::BasicBlock {
                            statements: successor_statements,
                            successor: vir_low::Successor::Goto(successor_label),
                        },
                    );
                }
            }

            basic_blocks.insert(
                label,
                vir_low::BasicBlock {
                    statements,
                    successor,
                },
            );
        }
        let entry = procedure.entry.clone().into_low(&mut self)?;
        let exit = procedure.exit.clone().into_low(&mut self)?;
        let mut removed_functions = FxHashSet::default();
        if procedure.check_mode == CheckMode::PurificationFunctional {
            removed_functions.insert(self.encode_memory_block_bytes_function_name()?);
        }
        let (mut predicates, predicates_info) = self.collect_owned_predicate_decls()?;
        basic_blocks.get_mut(&entry).unwrap().statements.splice(
            0..0,
            self.lifetimes_state.lifetime_is_alive_initialization(),
        );
        if prusti_common::config::dump_debug_info() {
            let source_filename = self.encoder.env().name.source_file_name();
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_before_perm_desugaring",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| basic_blocks.to_graphviz(writer).unwrap(),
            );
        }
        let mut domains = self.domains_state.destruct();
        domains.extend(self.compute_address_state.destruct());
        predicates.extend(self.predicates_state.destruct());
        let mut lowered_procedure = vir_low::ProcedureDecl {
            name: procedure.name,
            position: procedure.position,
            locals: self.variables_state.destruct(),
            custom_labels: self.labels_state.destruct(),
            basic_blocks,
            entry,
            exit,
        };
        let mut methods = self.methods_state.destruct();
        let mut functions = self.functions_state.destruct();
        if procedure.check_mode == CheckMode::PurificationFunctional {
            removed_functions.extend(
                functions
                    .iter()
                    .filter(|function| function.kind == vir_low::FunctionKind::Snap)
                    .map(|function| function.name.clone()),
            );
            super::transformations::remove_predicates::remove_predicates(
                &mut lowered_procedure,
                &mut methods,
                &removed_functions,
                std::mem::take(&mut predicates),
            );
            functions.retain(|function| !removed_functions.contains(&function.name));
        };
        let mut result = LoweringResult {
            procedures: vec![lowered_procedure],
            domains,
            functions,
            predicates,
            methods,
        };
        if prusti_common::config::custom_heap_encoding() {
            super::transformations::custom_heap_encoding::custom_heap_encoding(
                self.encoder,
                &mut result,
                predicates_info,
            )?;
        }
        Ok(result)
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

    /// If `check_copy` is true, encode `copy` builtin method.
    fn lower_type(
        mut self,
        def_id: Option<DefId>,
        ty: vir_mid::Type,
        check_copy: bool,
    ) -> SpannedEncodingResult<LoweringResult> {
        self.def_id = def_id;
        self.mark_owned_non_aliased_as_unfolded(&ty)?;
        self.encode_move_place_method(&ty)?;
        if check_copy {
            self.encode_copy_place_method(&ty)?;
        }
        let (mut predicates, _) = self.collect_owned_predicate_decls()?;
        let mut domains = self.domains_state.destruct();
        domains.extend(self.compute_address_state.destruct());
        predicates.extend(self.predicates_state.destruct());
        Ok(LoweringResult {
            procedures: Vec::new(),
            domains,
            functions: self.functions_state.destruct(),
            predicates,
            methods: self.methods_state.destruct(),
        })
    }
}
