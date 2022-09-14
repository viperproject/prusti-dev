mod statements;
mod pure_expressions;
mod heap;
mod effects;
mod predicates;
mod permission_mask;

use self::predicates::Predicates;
use super::variable_declarations::VariableDeclarations;
use crate::encoder::{
    errors::SpannedEncodingResult, middle::core_proof::predicates::OwnedPredicateInfo, Encoder,
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::BTreeMap;
use vir_crate::low::{self as vir_low};

pub(super) struct HeapEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p mut Encoder<'v, 'tcx>,
    new_variables: VariableDeclarations,
    predicates: Predicates<'p>,
    functions: FxHashMap<String, &'p vir_low::FunctionDecl>,
    ssa_state: vir_low::ssa::SSAState<vir_low::Label>,
    permission_mask_names: FxHashMap<String, String>,
    heap_names: FxHashMap<String, String>,
    /// A counter used for generating fresh labels.
    fresh_label_counter: u64,
}

impl<'p, 'v: 'p, 'tcx: 'v> HeapEncoder<'p, 'v, 'tcx> {
    pub(super) fn new(
        encoder: &'p mut Encoder<'v, 'tcx>,
        predicates: &'p [vir_low::PredicateDecl],
        predicate_info: BTreeMap<String, OwnedPredicateInfo>,
        functions: &'p [vir_low::FunctionDecl],
    ) -> Self {
        Self {
            encoder,
            new_variables: Default::default(),
            permission_mask_names: predicates
                .iter()
                .map(|predicate| {
                    let mask_name = format!("perm${}", predicate.name);
                    (predicate.name.clone(), mask_name)
                })
                .collect(),
            heap_names: predicates
                .iter()
                .map(|predicate| {
                    let heap_name = format!("heap${}", predicate.name);
                    (predicate.name.clone(), heap_name)
                })
                .collect(),
            predicates: Predicates::new(predicates, predicate_info),
            functions: functions
                .iter()
                .map(|function| (function.name.clone(), function))
                .collect(),
            ssa_state: Default::default(),
            fresh_label_counter: 0,
        }
    }

    pub(super) fn reset(&mut self) {
        self.new_variables = Default::default();
        self.ssa_state = Default::default();
        self.fresh_label_counter = 0;
    }

    pub(super) fn encode_statement(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        statement: vir_low::Statement,
    ) -> SpannedEncodingResult<()> {
        self.encode_statement_internal(statements, statement)
    }

    pub(super) fn prepare_new_current_block(
        &mut self,
        label: &vir_low::Label,
        predecessors: &BTreeMap<vir_low::Label, Vec<vir_low::Label>>,
        basic_block_edges: &mut BTreeMap<
            vir_low::Label,
            BTreeMap<vir_low::Label, Vec<(String, vir_low::Type, vir_low::Position, u64, u64)>>,
        >,
    ) -> SpannedEncodingResult<()> {
        self.ssa_state
            .prepare_new_current_block(label, predecessors, basic_block_edges);
        Ok(())
    }

    pub(super) fn finish_current_block(
        &mut self,
        label: vir_low::Label,
    ) -> SpannedEncodingResult<()> {
        self.ssa_state.finish_current_block(label);
        Ok(())
    }

    pub(super) fn generate_init_permissions_to_zero(
        &mut self,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Vec<vir_low::Statement>> {
        self.generate_init_permissions_to_zero_internal(position)
    }

    pub(super) fn generate_necessary_domains(
        &self,
    ) -> SpannedEncodingResult<Vec<vir_low::DomainDecl>> {
        let mut domains = Vec::new();
        self.generate_permission_mask_domains(&mut domains)?;
        self.generate_heap_domains(&mut domains)?;
        Ok(domains)
    }

    pub(super) fn create_variable(
        &mut self,
        variable_name: &str,
        ty: vir_low::Type,
        version: u64,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        self.new_variables
            .create_variable(variable_name, ty, version)
    }

    pub(super) fn take_variables(&mut self) -> FxHashSet<vir_low::VariableDecl> {
        self.new_variables.take_variables()
    }

    pub(super) fn encoder(&mut self) -> &mut Encoder<'v, 'tcx> {
        self.encoder
    }

    fn fresh_label(&mut self) -> String {
        self.fresh_label_counter += 1;
        format!("heap_label${}", self.fresh_label_counter)
    }
}
