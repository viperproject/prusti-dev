use std::collections::{BTreeMap, BTreeSet};

use super::{super::super::encoder_context::EncoderContext, ProcedureExecutor};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::symbolic_execution_new::expression_interner::ExpressionId,
};
use vir_crate::{
    common::{cfg::Cfg, expression::SyntacticEvaluation},
    low::{self as vir_low, operations::ty::Typed},
};

mod block;
mod merge_report;
mod equality_manager;
mod consistency_tracker;
mod visited_blocks;

pub(super) use self::{block::BlockConstraints, merge_report::ConstraintsMergeReport};

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn path_constraints_inconsistent(&self) -> SpannedEncodingResult<bool> {
        self.current_block_constraints().is_inconsistent()
    }

    pub(super) fn try_assume_heap_independent_conjuncts(
        &mut self,
        expression: &vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        match expression {
            vir_low::Expression::BinaryOp(binary_expression) => match binary_expression.op_kind {
                vir_low::BinaryOpKind::EqCmp => {
                    self.try_assume_equal(&binary_expression.left, &binary_expression.right)?;
                    return Ok(());
                }
                vir_low::BinaryOpKind::And => {
                    self.try_assume_heap_independent_conjuncts(&binary_expression.left)?;
                    self.try_assume_heap_independent_conjuncts(&binary_expression.right)?;
                    return Ok(());
                }
                _ => {}
            },

            _ => {}
        }
        self.try_assume(expression, true)?;
        Ok(())
    }

    fn try_assume_equal(
        &mut self,
        left: &vir_low::Expression,
        right: &vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        if left.is_term() && right.is_term() {
            debug_assert_eq!(left.get_type(), right.get_type());
            let current_block = self.current_block.as_ref().unwrap();
            let current_constraints =
                &mut self.state_keeper.get_state_mut(current_block).constraints;
            current_constraints.assume_equal(&mut self.expression_interner, left, right)?;
        }
        Ok(())
    }

    fn try_assume(
        &mut self,
        expression: &vir_low::Expression,
        value: bool,
    ) -> SpannedEncodingResult<()> {
        if expression.is_term() {
            match expression {
                vir_low::Expression::UnaryOp(unary_expression) => match unary_expression.op_kind {
                    vir_low::UnaryOpKind::Not => {
                        self.try_assume(&unary_expression.argument, !value)?;
                        return Ok(());
                    }
                    _ => {}
                },
                vir_low::Expression::Local(_) => {
                    self.assume(expression, value)?;
                }
                _ if expression.is_false() && value => {
                    self.assume_false()?;
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn assume_false(&mut self) -> SpannedEncodingResult<()> {
        let current_constraints = self.current_block_constraints_mut();
        current_constraints.assume_false()?;
        Ok(())
    }

    fn assume(
        &mut self,
        expression: &vir_low::Expression,
        value: bool,
    ) -> SpannedEncodingResult<()> {
        debug_assert!(expression.is_heap_independent());
        let expression_id = self
            .expression_interner
            .intern_bool_expression(expression)?;
        let current_constraints = self.current_block_constraints_mut();
        current_constraints.assume(expression, expression_id, value)?;
        if !current_constraints.is_inconsistent()? {
            let current_constraints = self.current_block_constraints();
            let result = self.check_inconsistencies_with_visited_blocks(
                current_constraints.get_visited_blocks(),
                expression_id,
                value,
            )?;
            if let Some((new_visited_blocks, new_dominators)) = result {
                let mut equalities = BTreeMap::new();
                for new_dominator in new_dominators {
                    let dominator_equalities = self
                        .state_keeper
                        .get_state(&new_dominator)
                        .constraints
                        .get_equalities()?;
                    equalities.insert(new_dominator, dominator_equalities);
                }
                let current_block = self.current_block.as_ref().unwrap();
                let current_constraints =
                    &mut self.state_keeper.get_state_mut(current_block).constraints;
                current_constraints.set_visited_blocks(new_visited_blocks);
                for (dominator, dominator_equalities) in &equalities {
                    for (left, right) in dominator_equalities {
                        current_constraints.assume_equal(
                            &mut self.expression_interner,
                            left,
                            right,
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    fn check_inconsistencies_with_visited_blocks(
        &self,
        visited_blocks: &BTreeSet<vir_low::Label>,
        expression_id: ExpressionId,
        value: bool,
    ) -> SpannedEncodingResult<Option<(BTreeSet<vir_low::Label>, BTreeSet<vir_low::Label>)>> {
        let mut inconsistent_blocks = BTreeSet::new();
        for visited_block in visited_blocks {
            let visited_block_constraints = &self.state_keeper.get_state(visited_block).constraints;
            if visited_block_constraints.assuming_makes_block_inconsistent(expression_id, value)? {
                inconsistent_blocks.insert(visited_block);
            }
        }
        if !inconsistent_blocks.is_empty() {
            let current_label = self.current_block.as_ref().unwrap();
            let mut new_visited_blocks = self
                .procedure
                .find_reaching(current_label, &inconsistent_blocks);
            assert!(new_visited_blocks.remove(current_label));
            new_visited_blocks.retain(|label| visited_blocks.contains(label));
            let old_dominators = self
                .procedure
                .compute_dominators_considering(current_label, visited_blocks);
            let mut new_dominators = self
                .procedure
                .compute_dominators_considering(current_label, &new_visited_blocks);
            new_dominators.retain(|dominator| !old_dominators.contains(dominator));
            Ok(Some((new_visited_blocks, new_dominators)))
        } else {
            Ok(None)
        }
    }

    fn current_block_constraints_mut(&mut self) -> &mut BlockConstraints {
        &mut self.current_state_mut().constraints
    }

    fn current_block_constraints(&self) -> &BlockConstraints {
        &self.current_state().constraints
    }
}
