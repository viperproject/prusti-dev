use super::EGraphState;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::{
        encoder_context::EncoderContext, symbolic_execution_new::program_context::ProgramContext,
    },
};
use rustc_hash::{FxHashMap, FxHashSet};
use vir_crate::low::{self as vir_low};

/// Provides an interface over an EGraph that operates on `vir_low::Expression`.
#[derive(Clone)]
pub(in super::super) struct ExpressionEGraph {
    /// The EGraph.
    egraph: EGraphState,
    /// The variables that were interned into the Egraph.
    interned_variables: FxHashSet<vir_low::VariableDecl>,
    /// The equalities that were assumed to hold between variables.
    assumed_variable_equalities: FxHashSet<(vir_low::VariableDecl, vir_low::VariableDecl)>,
}

pub(in super::super) struct IntersectingReport {
    pub(in super::super) self_dropped_variables: Vec<vir_low::VariableDecl>,
    pub(in super::super) other_dropped_variables: Vec<vir_low::VariableDecl>,
    /// The equalities between non-dropped variables that were dropped.
    pub(in super::super) self_dropped_equalities:
        Vec<(vir_low::VariableDecl, vir_low::VariableDecl)>,
    /// The equalities between non-dropped variables that were dropped.
    pub(in super::super) other_dropped_equalities:
        Vec<(vir_low::VariableDecl, vir_low::VariableDecl)>,
}

/// State management.
impl ExpressionEGraph {
    pub(in super::super) fn new(
        program_context: &ProgramContext<impl EncoderContext>,
    ) -> SpannedEncodingResult<Self> {
        let (bool_type, bool_domain_info) = program_context.get_bool_domain_info();
        let mut egraph =
            EGraphState::new(program_context.get_domains(), bool_type, bool_domain_info)?;
        // Assume which addresses are non-aliased.
        // FIXME: This could be a separate global EGraph because non-aliasing
        // information is static.
        for address in program_context.get_non_aliased_memory_block_addresses() {
            assert!(address.is_heap_independent());
            use vir_low::macros::*;
            let address_is_non_aliased = ty!(Bool);
            let address_non_aliased_call = expr! {
                (ComputeAddress::address_is_non_aliased([address.clone()]))
            };
            let address_id = egraph.try_intern_term(&address_non_aliased_call)?.unwrap();
            egraph.assume_equal(address_id, egraph.non_aliased_address_id)?;
        }
        Ok(Self {
            egraph,
            interned_variables: Default::default(),
            assumed_variable_equalities: Default::default(),
        })
    }

    /// Intersect the equalities of the egraph with the given egraph. Used by
    /// state merging.
    pub(in super::super) fn intersect_with(
        &mut self,
        other: &ExpressionEGraph,
    ) -> SpannedEncodingResult<IntersectingReport> {
        let self_dropped_variables = self
            .interned_variables
            .drain_filter(|variable| !other.interned_variables.contains(&variable))
            .collect();
        let other_dropped_variables = other
            .interned_variables
            .iter()
            .filter(|expression| !self.interned_variables.contains(expression))
            .cloned()
            .collect();
        let self_dropped_equalities = self
            .assumed_variable_equalities
            .drain_filter(|equality| !other.assumed_variable_equalities.contains(equality))
            .filter(|(left, right)| {
                self.interned_variables.contains(left) && self.interned_variables.contains(right)
            })
            .collect();
        let other_dropped_equalities = other
            .assumed_variable_equalities
            .iter()
            .filter(|equality| !self.assumed_variable_equalities.contains(equality))
            .filter(|(left, right)| {
                self.interned_variables.contains(left) && self.interned_variables.contains(right)
            })
            .cloned()
            .collect();
        let _ = self.egraph.intersect_with(&other.egraph)?;
        let report = IntersectingReport {
            self_dropped_variables,
            other_dropped_variables,
            self_dropped_equalities,
            other_dropped_equalities,
        };
        Ok(report)
    }

    pub(in super::super) fn contains(&self, variable: &vir_low::VariableDecl) -> bool {
        self.interned_variables.contains(variable)
    }
}

/// Interning expressions.
impl ExpressionEGraph {
    fn intern(&mut self, expression: &vir_low::Expression) -> SpannedEncodingResult<egg::Id> {
        assert!(
            expression.is_heap_independent(),
            "expression: {}",
            expression
        );
        let id = self.egraph.try_intern_term(expression)?.unwrap_or_else(|| {
            panic!("expression {expression} cannot be interned");
        });
        if let vir_low::Expression::Local(local) = expression {
            if !self.interned_variables.contains(&local.variable) {
                self.interned_variables.insert(local.variable.clone());
            }
        }
        Ok(id)
    }
}

/// Equalities.
impl ExpressionEGraph {
    pub(in super::super) fn assume_equal(
        &mut self,
        left: &vir_low::Expression,
        right: &vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        match (left, right) {
            (vir_low::Expression::Local(left_local), vir_low::Expression::Local(right_local)) => {
                self.assumed_variable_equalities
                    .insert((left_local.variable.clone(), right_local.variable.clone()));
                self.assumed_variable_equalities
                    .insert((right_local.variable.clone(), left_local.variable.clone()));
            }
            _ => {}
        }
        let left_id = self.intern(left)?;
        let right_id = self.intern(right)?;
        self.egraph.assume_equal(left_id, right_id)?;
        Ok(())
    }

    pub(in super::super) fn is_equal(
        &mut self,
        left: &vir_low::Expression,
        right: &vir_low::Expression,
    ) -> SpannedEncodingResult<bool> {
        let left_id = self.intern(left)?;
        let right_id = self.intern(right)?;
        self.saturate_solver()?;
        self.egraph.is_equal(left_id, right_id)
    }

    pub(in super::super) fn is_non_aliased_address(
        &mut self,
        address: &vir_low::Expression,
    ) -> SpannedEncodingResult<bool> {
        let address_id = self.intern(address)?;
        if self
            .egraph
            .is_equal(address_id, self.egraph.non_aliased_address_id)?
        {
            return Ok(true);
        } else {
            self.saturate_solver()?;
            self.egraph
                .is_equal(address_id, self.egraph.non_aliased_address_id)
        }
    }

    pub(in super::super) fn resolve_constant(
        &mut self,
        expression: &vir_low::Expression,
        constant_constructors: &FxHashSet<String>,
    ) -> SpannedEncodingResult<Option<(Option<String>, vir_low::Expression)>> {
        let id = self.intern(expression)?;
        self.egraph.resolve_constant(id, constant_constructors)
    }

    pub(in super::super) fn saturate_solver(&mut self) -> SpannedEncodingResult<()> {
        self.egraph.saturate()
    }
}
