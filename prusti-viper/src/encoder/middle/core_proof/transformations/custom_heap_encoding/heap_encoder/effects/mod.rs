use super::{
    permission_mask::{
        PermissionMaskKind, PermissionMaskKindAliasedBool,
        PermissionMaskKindAliasedFractionalBoundedPerm, PermissionMaskOperations,
        PredicatePermissionMaskKind, TPermissionMaskOperations,
    },
    HeapEncoder,
};
use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, SyntacticEvaluation},
    low::{self as vir_low},
};

impl<'p, 'v: 'p, 'tcx: 'v> HeapEncoder<'p, 'v, 'tcx> {
    /// Note: this method assumes that it is called only as a top level assert
    /// because it performs creating a new permission mask and rolling it back.
    ///
    /// Note: this method also evaluates accessibility predicates in
    /// `expression_evaluation_state_label`.
    pub(super) fn encode_expression_assert(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        expression: vir_low::Expression,
        position: vir_low::Position,
        expression_evaluation_state_label: Option<String>,
    ) -> SpannedEncodingResult<()> {
        assert!(!position.is_default(), "expression: {expression}");
        if expression.is_pure() {
            let expression = self.encode_pure_expression(
                statements,
                expression,
                expression_evaluation_state_label,
                position,
            )?;
            statements.push(vir_low::Statement::assert(expression, position));
        } else {
            let check_point = self.fresh_label();
            self.ssa_state.save_state_at_label(check_point.clone());
            let evaluation_state = if let Some(label) = &expression_evaluation_state_label {
                // This call is needed because we want to evaluate the
                // accessibility predicates in the specified state.
                self.ssa_state.change_state_to_label(label);
                label
            } else {
                &check_point
            };
            self.encode_expression_exhale(statements, expression, position, evaluation_state)?;
            self.ssa_state.change_state_to_label(&check_point);
        }
        Ok(())
    }

    /// This method is similar to `encode_expression_assert` but it is intended
    /// for asserting function preconditions. The key difference between
    /// asserting function preconditions and regular assert statements is that
    /// in function preconditions we ignore the permission amounts used in the
    /// accessibility predicates: we only check that the permission amounts are
    /// positive.
    pub(super) fn encode_function_precondition_assert(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        expression: vir_low::Expression,
        position: vir_low::Position,
        expression_evaluation_state_label: Option<String>,
    ) -> SpannedEncodingResult<()> {
        assert!(!position.is_default(), "expression: {expression}");
        if expression.is_pure() {
            let expression = self.encode_pure_expression(
                statements,
                expression,
                expression_evaluation_state_label,
                position,
            )?;
            statements.push(vir_low::Statement::assert(expression, position));
        } else {
            let check_point = self.fresh_label();
            self.ssa_state.save_state_at_label(check_point.clone());
            let evaluation_state = if let Some(label) = &expression_evaluation_state_label {
                // This call is needed because we want to evaluate the
                // accessibility predicates in the specified state.
                self.ssa_state.change_state_to_label(label);
                label
            } else {
                &check_point
            };
            self.encode_function_precondition_assert_rec(
                statements,
                expression,
                position,
                evaluation_state,
            )?;
            self.ssa_state.change_state_to_label(&check_point);
        }
        Ok(())
    }

    pub(super) fn encode_function_precondition_assert_rec(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        expression: vir_low::Expression,
        position: vir_low::Position,
        expression_evaluation_state_label: &str,
    ) -> SpannedEncodingResult<()> {
        assert!(!position.is_default(), "expression: {expression}");
        if expression.is_pure() {
            let expression = self.encode_pure_expression(
                statements,
                expression,
                Some(expression_evaluation_state_label.to_string()),
                position,
            )?;
            statements.push(vir_low::Statement::assert(expression, position));
        } else {
            match expression {
                vir_low::Expression::PredicateAccessPredicate(expression) => {
                    // FIXME: evaluate predicate arguments in expression_evaluation_state_label
                    match self.get_predicate_permission_mask_kind(&expression.name)? {
                        PredicatePermissionMaskKind::AliasedWholeBool
                        | PredicatePermissionMaskKind::AliasedFractionalBool => {
                            let operations =
                                PermissionMaskOperations::<PermissionMaskKindAliasedBool>::new(
                                    self,
                                    statements,
                                    &expression,
                                    Some(expression_evaluation_state_label.to_string()),
                                    position,
                                )?;
                            self.encode_function_precondition_assert_rec_predicate(
                                statements,
                                &expression,
                                position,
                                operations,
                            )?
                        }
                        PredicatePermissionMaskKind::AliasedFractionalBoundedPerm => {
                            let operations = PermissionMaskOperations::<
                                PermissionMaskKindAliasedFractionalBoundedPerm,
                            >::new(
                                self,
                                statements,
                                &expression,
                                Some(expression_evaluation_state_label.to_string()),
                                position,
                            )?;
                            self.encode_function_precondition_assert_rec_predicate(
                                statements,
                                &expression,
                                position,
                                operations,
                            )?
                        }
                        PredicatePermissionMaskKind::AliasedWholeNat => unimplemented!(),
                    }
                }
                vir_low::Expression::Unfolding(_) => todo!(),
                vir_low::Expression::LabelledOld(_) => todo!(),
                vir_low::Expression::BinaryOp(expression) => match expression.op_kind {
                    vir_low::BinaryOpKind::And => {
                        self.encode_function_precondition_assert_rec(
                            statements,
                            *expression.left,
                            position,
                            expression_evaluation_state_label,
                        )?;
                        self.encode_function_precondition_assert_rec(
                            statements,
                            *expression.right,
                            position,
                            expression_evaluation_state_label,
                        )?;
                    }
                    vir_low::BinaryOpKind::Implies if expression.left.is_true() => {
                        self.encode_function_precondition_assert_rec(
                            statements,
                            *expression.right,
                            position,
                            expression_evaluation_state_label,
                        )?;
                    }
                    vir_low::BinaryOpKind::Implies => {
                        let mut then_branch = Vec::new();
                        self.encode_function_precondition_assert_rec(
                            &mut then_branch,
                            *expression.right,
                            position,
                            expression_evaluation_state_label,
                        )?;
                        let guard = self.encode_pure_expression(
                            statements,
                            *expression.left,
                            Some(expression_evaluation_state_label.to_string()),
                            position,
                        )?;
                        statements.push(vir_low::Statement::conditional(
                            guard,
                            then_branch,
                            Vec::new(),
                            position,
                        ));
                    }
                    _ => unreachable!("expression: {}", expression),
                },
                vir_low::Expression::Conditional(_) => todo!(),
                vir_low::Expression::FuncApp(_) => todo!(),
                vir_low::Expression::DomainFuncApp(_) => todo!(),
                _ => {
                    unimplemented!("expression: {:?}", expression);
                }
            }
        }
        Ok(())
    }

    fn encode_function_precondition_assert_rec_predicate<Kind: PermissionMaskKind>(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        position: vir_low::Position,
        operations: PermissionMaskOperations<Kind>,
    ) -> SpannedEncodingResult<()>
    where
        PermissionMaskOperations<Kind>: TPermissionMaskOperations,
    {
        statements.push(vir_low::Statement::comment(format!(
            "assert-function-precondition-predicate {predicate}"
        )));
        // assert perm<P>(r1, r2, v_old) >= p
        statements.push(vir_low::Statement::assert(
            operations.perm_old_positive(),
            position, // FIXME: use position of expression.permission with proper ErrorCtxt.
        ));
        Ok(())
    }

    pub(super) fn encode_expression_exhale(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        expression: vir_low::Expression,
        position: vir_low::Position,
        expression_evaluation_state_label: &str,
    ) -> SpannedEncodingResult<()> {
        assert!(!position.is_default(), "expression: {expression}");
        if expression.is_pure() {
            let expression = self.encode_pure_expression(
                statements,
                expression,
                Some(expression_evaluation_state_label.to_string()),
                position,
            )?;
            statements.push(vir_low::Statement::assert(expression, position));
        } else {
            match expression {
                vir_low::Expression::PredicateAccessPredicate(expression) => {
                    // FIXME: evaluate predicate arguments in expression_evaluation_state_label
                    match self.get_predicate_permission_mask_kind(&expression.name)? {
                        PredicatePermissionMaskKind::AliasedWholeBool
                        | PredicatePermissionMaskKind::AliasedFractionalBool => {
                            let operations =
                                PermissionMaskOperations::<PermissionMaskKindAliasedBool>::new(
                                    self,
                                    statements,
                                    &expression,
                                    Some(expression_evaluation_state_label.to_string()),
                                    position,
                                )?;
                            self.encode_expression_exhale_predicate(
                                statements,
                                &expression,
                                position,
                                Some(expression_evaluation_state_label.to_string()),
                                operations,
                            )?
                        }
                        PredicatePermissionMaskKind::AliasedFractionalBoundedPerm => {
                            let operations = PermissionMaskOperations::<
                                PermissionMaskKindAliasedFractionalBoundedPerm,
                            >::new(
                                self,
                                statements,
                                &expression,
                                Some(expression_evaluation_state_label.to_string()),
                                position,
                            )?;
                            self.encode_expression_exhale_predicate(
                                statements,
                                &expression,
                                position,
                                Some(expression_evaluation_state_label.to_string()),
                                operations,
                            )?
                        }
                        PredicatePermissionMaskKind::AliasedWholeNat => unimplemented!(),
                    }
                }
                vir_low::Expression::Unfolding(_) => todo!(),
                vir_low::Expression::LabelledOld(_) => todo!(),
                vir_low::Expression::BinaryOp(expression) => match expression.op_kind {
                    vir_low::BinaryOpKind::And => {
                        self.encode_expression_exhale(
                            statements,
                            *expression.left,
                            position,
                            expression_evaluation_state_label,
                        )?;
                        self.encode_expression_exhale(
                            statements,
                            *expression.right,
                            position,
                            expression_evaluation_state_label,
                        )?;
                    }
                    vir_low::BinaryOpKind::Implies if expression.left.is_true() => {
                        self.encode_expression_exhale(
                            statements,
                            *expression.right,
                            position,
                            expression_evaluation_state_label,
                        )?;
                    }
                    vir_low::BinaryOpKind::Implies => {
                        unimplemented!("Merge the heap versions in the commented out code below.");
                        // let guard = self.encode_pure_expression(
                        //     statements,
                        //     *expression.left,
                        //     Some(expression_evaluation_state_label.to_string()),
                        //     position,
                        // )?;
                        // let mut body = Vec::new();
                        // self.encode_expression_exhale(
                        //     &mut body,
                        //     *expression.right,
                        //     position,
                        //     expression_evaluation_state_label,
                        // )?;
                        // // FIXME: Permission mask and heap versions need to be
                        // // unified after the branch merge.
                        // statements.push(vir_low::Statement::conditional(
                        //     guard,
                        //     body,
                        //     Vec::new(),
                        //     position,
                        // ))
                    }
                    _ => unreachable!("expression: {}", expression),
                },
                vir_low::Expression::Conditional(_) => todo!(),
                vir_low::Expression::FuncApp(_) => todo!(),
                vir_low::Expression::DomainFuncApp(_) => todo!(),
                _ => {
                    unimplemented!("expression: {:?}", expression);
                }
            }
        }
        Ok(())
    }

    fn encode_expression_exhale_predicate<Kind: PermissionMaskKind>(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        position: vir_low::Position,
        expression_evaluation_state_label: Option<String>,
        operations: PermissionMaskOperations<Kind>,
    ) -> SpannedEncodingResult<()>
    where
        PermissionMaskOperations<Kind>: TPermissionMaskOperations,
    {
        statements.push(vir_low::Statement::comment(format!(
            "exhale-predicate {predicate}"
        )));
        // assert perm<P>(r1, r2, v_old) >= p
        statements.push(vir_low::Statement::assert(
            operations.perm_old_greater_equals(&predicate.permission),
            position, // FIXME: use position of expression.permission with proper ErrorCtxt.
        ));
        let perm_new_value = operations.perm_old_sub(&predicate.permission);
        // assume perm<P>(r1, r2, v_new) == perm<P>(r1, r2, v_old) - p
        statements.push(vir_low::Statement::assume(
            vir_low::Expression::equals(operations.perm_new(), perm_new_value.clone()),
            position, // FIXME: use position of expression.permission with proper ErrorCtxt.
        ));
        // assume forall arg1: Ref, arg2: Ref ::
        //     {perm<P>(arg1, arg2, v_new)}
        //     !(r1 == arg1 && r2 == arg2) ==>
        //     perm<P>(arg1, arg2, v_new) == perm<P>(arg1, arg2, v_old)
        self.encode_perm_unchanged_quantifier(
            statements,
            predicate,
            operations.old_permission_mask_version(),
            operations.new_permission_mask_version(),
            position,
            expression_evaluation_state_label,
            perm_new_value,
        )?;
        // assume forall arg1: Ref, arg2: Ref ::
        //     {heap<P>(arg1, arg2, vh_new)}
        //     perm<P>(arg1, arg2, v_new) > 0 ==>
        //     heap<P>(arg1, arg2, vh_new) == heap<P>(arg1, arg2, vh_old)
        self.encode_heap_unchanged_quantifier(
            statements,
            predicate,
            operations.new_permission_mask_version(),
            position,
        )?;
        Ok(())
    }

    pub(super) fn encode_expression_inhale(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        expression: vir_low::Expression,
        position: vir_low::Position,
        expression_evaluation_state_label: Option<String>,
    ) -> SpannedEncodingResult<()> {
        if expression.is_pure() {
            let expression = self.encode_pure_expression(
                statements,
                expression,
                expression_evaluation_state_label,
                position,
            )?;
            statements.push(vir_low::Statement::assume(expression, position));
        } else {
            match expression {
                vir_low::Expression::PredicateAccessPredicate(expression) => {
                    match self.get_predicate_permission_mask_kind(&expression.name)? {
                        PredicatePermissionMaskKind::AliasedWholeBool
                        | PredicatePermissionMaskKind::AliasedFractionalBool => {
                            let operations =
                                PermissionMaskOperations::<PermissionMaskKindAliasedBool>::new(
                                    self,
                                    statements,
                                    &expression,
                                    expression_evaluation_state_label.clone(),
                                    position,
                                )?;
                            self.encode_expression_inhale_predicate(
                                statements,
                                &expression,
                                position,
                                expression_evaluation_state_label,
                                operations,
                            )?
                        }
                        PredicatePermissionMaskKind::AliasedFractionalBoundedPerm => {
                            let operations = PermissionMaskOperations::<
                                PermissionMaskKindAliasedFractionalBoundedPerm,
                            >::new(
                                self,
                                statements,
                                &expression,
                                expression_evaluation_state_label.clone(),
                                position,
                            )?;
                            self.encode_expression_inhale_predicate(
                                statements,
                                &expression,
                                position,
                                expression_evaluation_state_label,
                                operations,
                            )?
                        }
                        PredicatePermissionMaskKind::AliasedWholeNat => unimplemented!(),
                    }
                }
                vir_low::Expression::Unfolding(_) => todo!(),
                vir_low::Expression::LabelledOld(_) => todo!(),
                vir_low::Expression::BinaryOp(expression) => match expression.op_kind {
                    vir_low::BinaryOpKind::And => {
                        self.encode_expression_inhale(
                            statements,
                            *expression.left,
                            position,
                            expression_evaluation_state_label.clone(),
                        )?;
                        self.encode_expression_inhale(
                            statements,
                            *expression.right,
                            position,
                            expression_evaluation_state_label,
                        )?;
                    }
                    vir_low::BinaryOpKind::Implies => {
                        let guard = self.encode_pure_expression(
                            statements,
                            *expression.left,
                            expression_evaluation_state_label.clone(),
                            position,
                        )?;
                        let mut body = Vec::new();
                        self.encode_expression_inhale(
                            &mut body,
                            *expression.right,
                            position,
                            expression_evaluation_state_label,
                        )?;
                        statements.push(vir_low::Statement::conditional(
                            guard,
                            body,
                            Vec::new(),
                            position,
                        ))
                    }
                    _ => unreachable!("expression: {}", expression),
                },
                vir_low::Expression::Conditional(_) => todo!(),
                vir_low::Expression::FuncApp(_) => todo!(),
                vir_low::Expression::DomainFuncApp(_) => todo!(),
                _ => {
                    unimplemented!("expression: {:?}", expression);
                }
            }
        }
        Ok(())
    }

    fn encode_expression_inhale_predicate<Kind: PermissionMaskKind>(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        position: vir_low::Position,
        expression_evaluation_state_label: Option<String>,
        operations: PermissionMaskOperations<Kind>,
    ) -> SpannedEncodingResult<()>
    where
        PermissionMaskOperations<Kind>: TPermissionMaskOperations,
    {
        statements.push(vir_low::Statement::comment(format!(
            "inhale-predicate {predicate}"
        )));
        if operations.can_assume_old_permission_is_none(&predicate.permission) {
            statements.push(vir_low::Statement::assume(
                operations.perm_old_equal_none(),
                position, // FIXME: use position of expression.permission with proper ErrorCtxt.
            ));
        }
        let perm_new_value = operations.perm_old_add(&predicate.permission);
        // assume perm<P>(r1, r2, v_new) == perm<P>(r1, r2, v_old) + p
        statements.push(vir_low::Statement::assume(
            vir_low::Expression::equals(operations.perm_new(), perm_new_value.clone()),
            position, // FIXME: use position of expression.permission with proper ErrorCtxt.
        ));
        // assume forall arg1: Ref, arg2: Ref ::
        //     {perm<P>(arg1, arg2, v_new)}
        //     !(r1 == arg1 && r2 == arg2) ==>
        //     perm<P>(arg1, arg2, v_new) == perm<P>(arg1, arg2, v_old)
        self.encode_perm_unchanged_quantifier(
            statements,
            predicate,
            operations.old_permission_mask_version(),
            operations.new_permission_mask_version(),
            position,
            expression_evaluation_state_label,
            perm_new_value,
        )?;
        Ok(())
    }
}
