use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::{
        encoder_context::EncoderContext,
        symbolic_execution_new::{
            egg::{ExpressionEGraph, IntersectingReport},
            expression_interner::ExpressionInterner,
            program_context::ProgramContext,
        },
    },
};
use log::debug;
use rustc_hash::{FxHashMap, FxHashSet};
use vir_crate::low::{self as vir_low};

/// A data structure for tracking equalities between expressions of the same
/// type. At a specific block, the equalities are tracked by using two data
/// structures:
///
/// 1. A log of equalities that have been seen so far.
/// 2. egg
///
/// Merging is done by intersecting incoming egraphs.
///         // TODO: I cannot use my interning tables!!! Need to reconstruct expression from the EGraph representation!!!
// TODO: Do in the same way as with lifetimes: keep a set of interened expressions and from that compute
// which were dropped. Also keep a sequence of SSA variable reassignments seen in the last block.
// For all dropped expressions construct a new expression with SSA reassignments and add it to the
// map of changed expressions.
// #[derive(Clone)]
pub(super) struct EqualityState {
    egraph: ExpressionEGraph,
    /// Equalities between variables assumed in the current block.
    variable_equalities_in_block: Vec<(vir_low::VariableDecl, vir_low::VariableDecl)>,
    equalities_in_block: Vec<(vir_low::Expression, vir_low::Expression)>,
}

impl Clone for EqualityState {
    fn clone(&self) -> Self {
        Self {
            egraph: self.egraph.clone(),
            variable_equalities_in_block: self.variable_equalities_in_block.clone(),
            equalities_in_block: Default::default(),
        }
    }
}

pub(super) struct EqualityStateMergeReport {
    pub(super) self_remaps: FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl>,
    pub(super) other_remaps: FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl>,
    pub(super) dropped_self_equalities: FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl>,
    pub(super) dropped_other_equalities: FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl>,
}

impl EqualityState {
    pub(super) fn new(
        program_context: &ProgramContext<impl EncoderContext>,
    ) -> SpannedEncodingResult<Self> {
        let egraph = ExpressionEGraph::new(program_context)?;
        Ok(Self {
            egraph,
            variable_equalities_in_block: Vec::new(),
            equalities_in_block: Vec::new(),
        })
    }
    // pub(super) fn set_final_egraph(&mut self, egraph: EGraphState) -> SpannedEncodingResult<()> {
    //     assert!(self.final_egraph.is_none());
    //     self.final_egraph = Some(egraph);
    //     Ok(())
    // }

    // pub(super) fn get_final_egraph(&self) -> SpannedEncodingResult<&EGraphState> {
    //     Ok(self.final_egraph.as_ref().unwrap())
    // }

    pub(super) fn saturate_solver(&mut self) -> SpannedEncodingResult<()> {
        self.egraph.saturate_solver()
    }

    pub(super) fn get_equalities(
        &self,
    ) -> SpannedEncodingResult<Vec<(vir_low::Expression, vir_low::Expression)>> {
        // let equalities = self
        //     .variable_equalities_in_block
        //     .iter()
        //     .map(|(left, right)| (left.clone().into(), right.clone().into()))
        //     .collect();
        // Ok(equalities)
        Ok(self.equalities_in_block.clone())
    }

    pub(super) fn is_non_aliased_address(
        &mut self,
        address: &vir_low::Expression,
    ) -> SpannedEncodingResult<bool> {
        self.egraph.is_non_aliased_address(address)
    }

    pub(super) fn assume_equal(
        &mut self,
        _expression_interner: &mut ExpressionInterner,
        left: &vir_low::Expression,
        right: &vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        self.equalities_in_block.push((left.clone(), right.clone()));
        self.egraph.assume_equal(left, right)?;
        match (left, right) {
            (vir_low::Expression::Local(left), vir_low::Expression::Local(right)) => {
                self.variable_equalities_in_block
                    .push((left.variable.clone(), right.variable.clone()));
            }
            _ => {}
        }
        Ok(())
    }

    pub(super) fn is_equal(
        &mut self,
        _expression_interner: &mut ExpressionInterner,
        left: &vir_low::Expression,
        right: &vir_low::Expression,
    ) -> SpannedEncodingResult<bool> {
        self.egraph.is_equal(left, right)
    }

    pub(super) fn resolve_constant(
        &mut self,
        expression: &vir_low::Expression,
        constant_constructors: &FxHashSet<String>,
    ) -> SpannedEncodingResult<Option<(Option<String>, vir_low::Expression)>> {
        self.egraph
            .resolve_constant(expression, constant_constructors)
    }

    pub(super) fn merge(
        &mut self,
        other: &Self,
    ) -> SpannedEncodingResult<EqualityStateMergeReport> {
        let IntersectingReport {
            self_dropped_variables,
            other_dropped_variables,
            self_dropped_equalities,
            other_dropped_equalities,
        } = self.egraph.intersect_with(&other.egraph)?;
        fn create_remap(
            dropped_variables: Vec<vir_low::VariableDecl>,
            variable_equalities_in_block: &[(vir_low::VariableDecl, vir_low::VariableDecl)],
            egraph: &ExpressionEGraph,
        ) -> FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl> {
            let mut remap = FxHashMap::default();
            let mut unmapped_variables = Vec::new();
            'outer: for variable in dropped_variables {
                for (left, right) in variable_equalities_in_block {
                    if &variable == right && egraph.contains(left) {
                        debug!("remapping {} to {}", variable, left);
                        remap.insert(variable, left.clone());
                        continue 'outer;
                    }
                    if &variable == left && egraph.contains(right) {
                        debug!("remapping {} to {}", variable, right);
                        remap.insert(variable, right.clone());
                        continue 'outer;
                    }
                }
                unmapped_variables.push(variable);
            }
            let mut remaps_added = true;
            while remaps_added {
                remaps_added = false;
                'outer: for variable in std::mem::take(&mut unmapped_variables) {
                    for (left, right) in variable_equalities_in_block {
                        if &variable == right {
                            if let Some(left_remap) = remap.get(left) {
                                debug!("remapping {} to {}", variable, left_remap);
                                remap.insert(variable, left_remap.clone());
                                remaps_added = true;
                                continue 'outer;
                            }
                        }
                        if &variable == left {
                            if let Some(right_remap) = remap.get(right) {
                                debug!("remapping {} to {}", variable, right_remap);
                                remap.insert(variable, right_remap.clone());
                                remaps_added = true;
                                continue 'outer;
                            }
                        }
                    }
                    unmapped_variables.push(variable);
                }
            }
            remap
        }
        let intersected_egraph = &self.egraph;
        let self_remaps = create_remap(
            self_dropped_variables,
            &self.variable_equalities_in_block,
            intersected_egraph,
        );
        let other_remaps = create_remap(
            other_dropped_variables,
            &other.variable_equalities_in_block,
            intersected_egraph,
        );
        let report = EqualityStateMergeReport {
            self_remaps,
            other_remaps,
            dropped_self_equalities: self_dropped_equalities.into_iter().collect(),
            dropped_other_equalities: other_dropped_equalities.into_iter().collect(),
        };
        Ok(report)
    }

    // pub(super) fn merge(&mut self, other: &Self) {
    //     // Intersect all the `equality_log` sets in the states.
    //     self.equality_log
    //         .retain(|equality| other.equality_log.contains(equality));
    //     // Reconstruct the union-find.
    //     self.union_find = InPlaceUnificationTable::new();
    //     self.expression_to_key = BTreeMap::new();
    //     for (left_expression_id, right_expression_id) in &self.equality_log {
    //         let left_key = *self
    //             .expression_to_key
    //             .entry(*left_expression_id)
    //             .or_insert_with(|| self.union_find.new_key(()));
    //         let right_key = *self
    //             .expression_to_key
    //             .entry(*right_expression_id)
    //             .or_insert_with(|| self.union_find.new_key(()));
    //         self.union_find.union(left_key, right_key);
    //     }
    // }
}
