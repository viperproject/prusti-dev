use std::collections::BTreeSet;

use super::{
    consistency_tracker::ConsistencyTracker,
    equality_manager::{EqualityState, EqualityStateMergeReport},
    merge_report::ConstraintsMergeReport,
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::{
        encoder_context::EncoderContext,
        symbolic_execution_new::{
            expression_interner::{ExpressionId, ExpressionInterner},
            program_context::ProgramContext,
        },
    },
};
use rustc_hash::{FxHashMap, FxHashSet};
use vir_crate::{
    common::expression::SyntacticEvaluation,
    low::{self as vir_low, operations::ty::Typed},
};

pub(in super::super) struct BlockConstraints {
    visited_blocks: BTreeSet<vir_low::Label>,
    /// Consistency tracker for the path up to this point.
    pub(super) consistency_tracker: ConsistencyTracker,
    /// Consistency tracker only for this block. The difference is achieved by
    /// overriding the `clone` method.
    pub(super) block_consistency_tracker: ConsistencyTracker,
    /// The lifetime equalities.
    pub(super) lifetime_equality_classes: FxHashMap<String, String>,
    /// The equalities of everything that are not lifetimes.
    pub(super) equality_classes: EqualityState,
}

impl Clone for BlockConstraints {
    fn clone(&self) -> Self {
        Self {
            visited_blocks: self.visited_blocks.clone(),
            block_consistency_tracker: Default::default(),
            consistency_tracker: self.consistency_tracker.clone(),
            lifetime_equality_classes: self.lifetime_equality_classes.clone(),
            equality_classes: self.equality_classes.clone(),
        }
    }
}

impl BlockConstraints {
    pub(in super::super) fn new(
        program_context: &ProgramContext<impl EncoderContext>,
    ) -> SpannedEncodingResult<Self> {
        let equality_classes = EqualityState::new(program_context)?;
        Ok(Self {
            visited_blocks: Default::default(),
            block_consistency_tracker: Default::default(),
            consistency_tracker: Default::default(),
            lifetime_equality_classes: FxHashMap::default(),
            equality_classes,
        })
    }

    pub(super) fn is_inconsistent(&self) -> SpannedEncodingResult<bool> {
        self.consistency_tracker.is_inconsistent()
    }

    pub(super) fn is_definitely_true(
        &self,
        expression: &vir_low::Expression,
        expression_id: ExpressionId,
    ) -> SpannedEncodingResult<bool> {
        self.consistency_tracker
            .is_definitely_true(expression, expression_id)
    }

    pub(super) fn is_definitely_false(
        &self,
        expression: &vir_low::Expression,
        expression_id: ExpressionId,
    ) -> SpannedEncodingResult<bool> {
        self.consistency_tracker
            .is_definitely_false(expression, expression_id)
    }

    pub(in super::super) fn assume_false(&mut self) -> SpannedEncodingResult<()> {
        self.block_consistency_tracker.assume_false()?;
        self.consistency_tracker.assume_false()
    }

    pub(super) fn assume(
        &mut self,
        expression: &vir_low::Expression,
        expression_id: ExpressionId,
        value: bool,
    ) -> SpannedEncodingResult<()> {
        self.block_consistency_tracker
            .assume(expression, expression_id, value)?;
        self.consistency_tracker
            .assume(expression, expression_id, value)
    }

    pub(super) fn assuming_makes_block_inconsistent(
        &self,
        expression_id: ExpressionId,
        value: bool,
    ) -> SpannedEncodingResult<bool> {
        self.consistency_tracker
            .assuming_makes_inconsistent(expression_id, value)
    }

    pub(in super::super) fn resolve_cannonical_lifetime_name(
        &self,
        lifetime_name: &str,
    ) -> SpannedEncodingResult<Option<&str>> {
        if let Some(cannonical_name) = self.lifetime_equality_classes.get(lifetime_name) {
            Ok(Some(&**cannonical_name))
        } else {
            Ok(None)
        }
    }

    pub(in super::super) fn get_equal_lifetimes(
        &self,
        lifetime_name: &str,
    ) -> SpannedEncodingResult<BTreeSet<String>> {
        let mut equality_class = BTreeSet::new();
        for (name, cannonical_name) in &self.lifetime_equality_classes {
            if cannonical_name == lifetime_name {
                equality_class.insert(name.clone());
            }
            if name == lifetime_name {
                equality_class.insert(cannonical_name.clone());
            }
        }
        equality_class.insert(lifetime_name.to_string());
        Ok(equality_class)
    }

    pub(in super::super) fn merge(
        &mut self,
        other: &Self,
    ) -> SpannedEncodingResult<ConstraintsMergeReport> {
        self.visited_blocks
            .extend(other.visited_blocks.iter().cloned());
        self.consistency_tracker.merge(&other.consistency_tracker)?;
        // Keep only the lifetime equalities that are present in both states.
        let dropped_self_lifetime_equalities = self
            .lifetime_equality_classes
            .drain_filter(|name, cannonical_name| {
                !other
                    .lifetime_equality_classes
                    .get(name)
                    .map(|other_cannonical_name| other_cannonical_name == cannonical_name)
                    .unwrap_or(false)
            })
            .map(|(name, cannonical_name)| (cannonical_name, name))
            .collect();
        let dropped_other_lifetime_equalities = other
            .lifetime_equality_classes
            .iter()
            .filter(|(name, cannonical_name)| {
                !self
                    .lifetime_equality_classes
                    .get(*name)
                    .map(|self_cannonical_name| self_cannonical_name == *cannonical_name)
                    .unwrap_or(false)
            })
            .map(|(name, cannonical_name)| (cannonical_name.clone(), name.clone()))
            .collect();
        // Merge equality graphs.
        let EqualityStateMergeReport {
            self_remaps,
            other_remaps,
            dropped_self_equalities,
            dropped_other_equalities,
        } = self.equality_classes.merge(&other.equality_classes)?;
        Ok(ConstraintsMergeReport {
            dropped_self_lifetime_equalities,
            dropped_other_lifetime_equalities,
            self_remaps,
            other_remaps,
            dropped_self_equalities,
            dropped_other_equalities,
        })
    }

    pub(in super::super) fn saturate_solver(&mut self) -> SpannedEncodingResult<()> {
        self.equality_classes.saturate_solver()
    }

    fn assume_lifetimes_equal(&mut self, left: &vir_low::Expression, right: &vir_low::Expression) {
        match (left, right) {
            (vir_low::Expression::Local(left), vir_low::Expression::Local(right)) => {
                let mut cannonical_name = &right.variable.name;
                while let Some(base) = self.lifetime_equality_classes.get(cannonical_name) {
                    cannonical_name = base;
                }
                self.lifetime_equality_classes
                    .insert(left.variable.name.clone(), cannonical_name.to_string());
            }
            _ => {
                // We do not track intersected lifetimes.
            }
        }
    }

    pub(super) fn get_equalities(
        &self,
    ) -> SpannedEncodingResult<Vec<(vir_low::Expression, vir_low::Expression)>> {
        self.equality_classes.get_equalities()
    }

    pub(in super::super) fn is_non_aliased_address(
        &mut self,
        address: &vir_low::Expression,
    ) -> SpannedEncodingResult<bool> {
        self.equality_classes.is_non_aliased_address(address)
    }

    pub(in super::super) fn assume_equal(
        &mut self,
        expression_interner: &mut ExpressionInterner,
        left: &vir_low::Expression,
        right: &vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        self.equality_classes
            .assume_equal(expression_interner, left, right)?;
        if left.get_type().is_lifetime() {
            self.assume_lifetimes_equal(left, right);
        }
        if left.get_type().is_bool() {
            let left_id = expression_interner.intern_bool_expression(left)?;
            let right_id = expression_interner.intern_bool_expression(right)?;
            if self.consistency_tracker.is_definitely_true(left, left_id)? {
                self.consistency_tracker.assume(right, right_id, true)?;
            }
            if self
                .consistency_tracker
                .is_definitely_false(left, left_id)?
            {
                self.consistency_tracker.assume(right, right_id, false)?;
            }
            if self
                .consistency_tracker
                .is_definitely_true(right, right_id)?
            {
                self.consistency_tracker.assume(left, left_id, true)?;
            }
            if self
                .consistency_tracker
                .is_definitely_false(right, right_id)?
            {
                self.consistency_tracker.assume(left, left_id, false)?;
            }
        }
        Ok(())
    }

    pub(in super::super) fn is_equal(
        &mut self,
        expression_interner: &mut ExpressionInterner,
        program_context: &ProgramContext<impl EncoderContext>,
        arg1: &vir_low::Expression,
        arg2: &vir_low::Expression,
    ) -> SpannedEncodingResult<bool> {
        let equal = if arg1 == arg2 {
            true
        } else {
            assert_eq!(arg1.get_type(), arg2.get_type());
            let ty = arg1.get_type();
            match ty {
                vir_low::Type::Int => todo!("{ty}"),
                vir_low::Type::Bool => {
                    let arg1_id = expression_interner.intern_bool_expression(arg1)?;
                    let arg2_id = expression_interner.intern_bool_expression(arg2)?;
                    let both_true = self.is_definitely_true(arg1, arg1_id)?
                        && self.is_definitely_true(arg2, arg2_id)?;
                    let both_false = self.is_definitely_false(arg1, arg1_id)?
                        && self.is_definitely_false(arg2, arg2_id)?;
                    both_true || both_false
                }
                vir_low::Type::Perm => todo!("{ty}"),
                vir_low::Type::Float(_) => todo!("{ty}"),
                vir_low::Type::BitVector(_) => todo!("{ty}"),
                vir_low::Type::Seq(_) => todo!("{ty}"),
                vir_low::Type::Set(_) => todo!("{ty}"),
                vir_low::Type::MultiSet(_) => todo!("{ty}"),
                vir_low::Type::Map(_) => todo!("{ty}"),
                vir_low::Type::Ref => todo!("{ty}"),
                vir_low::Type::Domain(_) if program_context.is_place_option_type(ty) => {
                    // Places have to be syntactically equal.
                    false
                }
                // vir_low::Type::Domain(_) if program_context.is_address_type(ty) => self
                //     .equality_classes
                //     .is_equal(expression_interner, arg1, arg2)?,
                // vir_low::Type::Domain(_) if program_context.is_lifetime_type(ty) => {
                //     let vir_low::Expression::Local(local1) = arg1 else {
                //         unreachable!("arg1: {arg1}");
                //     };
                //     let vir_low::Expression::Local(local2) = arg2 else {
                //         unreachable!("arg2: {arg2}");
                //     };
                //     let cannonical_arg1 =
                //         self.resolve_cannonical_lifetime_name(&local1.variable.name)?;
                //     let cannonical_arg2 =
                //         self.resolve_cannonical_lifetime_name(&local2.variable.name)?;
                //     match (cannonical_arg1, cannonical_arg2) {
                //         (Some(cannonical_arg1), Some(cannonical_arg2)) => {
                //             eprintln!("    {cannonical_arg1} == {cannonical_arg2}");
                //             cannonical_arg1 == cannonical_arg2
                //         }
                //         _ => self
                //             .equality_classes
                //             .is_equal(expression_interner, arg1, arg2)?,
                //     }
                // }
                vir_low::Type::Domain(_) => {
                    self.equality_classes
                        .is_equal(expression_interner, arg1, arg2)?
                }
            }
        };
        Ok(equal)
    }

    pub(in super::super) fn resolve_constant(
        &mut self,
        expression: &vir_low::Expression,
        constant_constructors: &FxHashSet<String>,
    ) -> SpannedEncodingResult<Option<(Option<String>, vir_low::Expression)>> {
        self.equality_classes
            .resolve_constant(expression, constant_constructors)
    }

    pub(in super::super) fn set_visited_block(&mut self, block: vir_low::Label) {
        assert!(self.visited_blocks.insert(block));
    }

    pub(in super::super) fn get_visited_blocks(&self) -> &BTreeSet<vir_low::Label> {
        &self.visited_blocks
    }

    pub(in super::super) fn set_visited_blocks(
        &mut self,
        new_visited_blocks: BTreeSet<vir_low::Label>,
    ) {
        assert!(new_visited_blocks.is_subset(&self.visited_blocks));
        self.visited_blocks = new_visited_blocks;
    }
}
