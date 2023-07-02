use super::{
    permission_mask::{
        PermissionMaskKind, PermissionMaskKindAliasedBool, PermissionMaskKindAliasedDuplicableBool,
        PermissionMaskKindAliasedFractionalBoundedPerm, PermissionMaskOperations,
        PredicatePermissionMaskKind, QuantifiedPermissionMaskOperations, TPermissionMaskOperations,
        TQuantifiedPermissionMaskOperations,
    },
    HeapEncoder,
};
use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::{
    common::expression::{
        BinaryOperationHelpers, ExpressionIterator, QuantifierHelpers, SyntacticEvaluation,
    },
    low::{self as vir_low, operations::ty::Typed},
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
            let expression = self.purify_snap_function_calls_in_expression(
                statements,
                expression,
                expression_evaluation_state_label,
                position,
                false,
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
            let expression = self.purify_snap_function_calls_in_expression(
                statements,
                expression,
                expression_evaluation_state_label,
                position,
                true,
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
            let expression = self.purify_snap_function_calls_in_expression(
                statements,
                expression,
                Some(evaluation_state.to_string()),
                position,
                true,
            )?;
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
            // let expression = self.purify_snap_function_calls_in_expression(
            //     statements,
            //     expression,
            //     Some(expression_evaluation_state_label.to_string()),
            //     position,
            //     true,
            // )?;
            statements.push(vir_low::Statement::assert(expression, position));
        } else {
            match expression {
                vir_low::Expression::PredicateAccessPredicate(mut expression) => {
                    // expression.arguments = self.purify_snap_function_calls_in_expressions(
                    //     statements,
                    //     expression.arguments,
                    //     Some(expression_evaluation_state_label.to_string()),
                    //     position,
                    //     true,
                    // )?;
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
                        PredicatePermissionMaskKind::AliasedWholeDuplicable => unimplemented!(),
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
                        // let guard = self.purify_snap_function_calls_in_expression(
                        //     statements,
                        //     *expression.left,
                        //     Some(expression_evaluation_state_label.to_string()),
                        //     position,
                        //     true,
                        // )?;
                        let guard = *expression.left;
                        statements.push(vir_low::Statement::conditional(
                            guard,
                            then_branch,
                            Vec::new(),
                            position,
                        ));
                    }
                    _ => unreachable!("expression: {}", expression),
                },
                vir_low::Expression::Quantifier(expression) => {
                    if let vir_low::Expression::BinaryOp(vir_low::BinaryOp {
                        op_kind: vir_low::BinaryOpKind::Implies,
                        left: box guard,
                        right: box vir_low::Expression::PredicateAccessPredicate(predicate),
                        ..
                    }) = *expression.body
                    {
                        self.create_quantifier_variables_remap(&expression.variables)?;
                        eprintln!("-----------------");
                        // let guard = self.purify_snap_function_calls_in_expression(
                        //     statements,
                        //     guard,
                        //     Some(expression_evaluation_state_label.to_string()),
                        //     position,
                        //     false,
                        // )?;
                        // FIXME: evaluate predicate arguments in expression_evaluation_state_label
                        match self.get_predicate_permission_mask_kind(&predicate.name)? {
                            PredicatePermissionMaskKind::AliasedWholeBool
                            | PredicatePermissionMaskKind::AliasedFractionalBool => {
                                let operations = QuantifiedPermissionMaskOperations::<
                                    PermissionMaskKindAliasedBool,
                                >::new(
                                    self,
                                    statements,
                                    &predicate,
                                    Some(expression_evaluation_state_label.to_string()),
                                    position,
                                )?;
                                self.encode_function_precondition_assert_rec_quantified_predicate(
                                    statements,
                                    expression.variables,
                                    guard,
                                    &predicate,
                                    expression.triggers,
                                    position,
                                    operations,
                                )?
                            }
                            PredicatePermissionMaskKind::AliasedFractionalBoundedPerm => {
                                let operations = QuantifiedPermissionMaskOperations::<
                                    PermissionMaskKindAliasedFractionalBoundedPerm,
                                >::new(
                                    self,
                                    statements,
                                    &predicate,
                                    Some(expression_evaluation_state_label.to_string()),
                                    position,
                                )?;
                                self.encode_function_precondition_assert_rec_quantified_predicate(
                                    statements,
                                    expression.variables,
                                    guard,
                                    &predicate,
                                    expression.triggers,
                                    position,
                                    operations,
                                )?
                            }
                            PredicatePermissionMaskKind::AliasedWholeDuplicable => unimplemented!(),
                        }
                        self.bound_variable_remap_stack.pop();
                    } else {
                        unimplemented!("expression: {:?}", expression);
                    }
                }
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

    // Note: This function does not check that permissions are disjoint, only
    // that we have enough. This is fine, because function preconditions only
    // need to be checked that we have some permission amount.
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

    // Note: This function does not check that permissions are disjoint, only
    // that we have enough. This is fine, because function preconditions only
    // need to be checked that we have some permission amount.
    fn encode_function_precondition_assert_rec_quantified_predicate<'a, Kind: PermissionMaskKind>(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        variables: Vec<vir_low::VariableDecl>,
        guard: vir_low::Expression,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        triggers: Vec<vir_low::Trigger>,
        position: vir_low::Position,
        operations: QuantifiedPermissionMaskOperations<'a, Kind>,
    ) -> SpannedEncodingResult<()>
    where
        QuantifiedPermissionMaskOperations<'a, Kind>: TQuantifiedPermissionMaskOperations,
    {
        // FIXME: Code duplication with encode_expression_inhale_quantified_predicate

        // FIXME: See whether I can skolemize out the quantifier into a single
        // assert statement.
        statements.push(vir_low::Statement::comment(format!(
            "assert-function-precondition-quantified-predicate {guard} ==> {predicate}"
        )));
        // Generate inverse functions for the variables.
        // ```
        // forall index: Int ::
        //    0 <= index && index < size ==>
        //    inverse$qp$P$index(offset(addr, index), Size$Pair()) == index
        // ```
        // Also construct the necessary parts for the permission mask update quantifier.
        let parameters: Vec<_> = predicate
            .arguments
            .iter()
            .enumerate()
            .map(|(index, argument)| {
                vir_low::VariableDecl::new(format!("_{index}"), argument.get_type().clone())
            })
            .collect();
        let parameters_as_arguments: Vec<_> = parameters
            .clone()
            .into_iter()
            .map(|parameter| parameter.into())
            .collect();
        let mut permission_mask_assert_trigger_terms = Vec::new();
        let mut permission_mask_assert_guard = guard.clone();
        let mut equalities: Vec<vir_low::Expression> = Vec::new();
        for variable in &variables {
            let inverse_function_name = format!(
                "inverse$qp${}${}${}",
                predicate.name,
                variable.name,
                self.inverse_function_domain.functions.len()
            );
            {
                // Declare the inverse function.
                let inverse_function = vir_low::DomainFunctionDecl::new(
                    inverse_function_name.clone(),
                    false,
                    parameters.clone(),
                    variable.ty.clone(),
                );
                let permission_mask_assert_inverse_function_call =
                    vir_low::Expression::domain_function_call(
                        self.inverse_function_domain.name.clone(),
                        inverse_function_name.clone(),
                        parameters_as_arguments.clone(),
                        variable.ty.clone(),
                    );
                permission_mask_assert_guard = permission_mask_assert_guard.replace_place(
                    &variable.clone().into(),
                    &permission_mask_assert_inverse_function_call,
                );
                permission_mask_assert_trigger_terms
                    .push(permission_mask_assert_inverse_function_call);
                self.inverse_function_domain
                    .functions
                    .push(inverse_function);
            }
            {
                // Declare the inverse function definitional equality.
                let inverse_function_call = vir_low::Expression::domain_function_call(
                    self.inverse_function_domain.name.clone(),
                    inverse_function_name,
                    predicate.arguments.clone(),
                    variable.ty.clone(),
                );
                eprintln!("inverse_function: {}", inverse_function_call);
                equalities.push(vir_low::Expression::equals(
                    variable.clone().into(),
                    inverse_function_call,
                ));
            }
        }
        // We are using skolemized variables, so inverse functions are not needed.
        // let axiom_body = vir_low::Expression::forall(
        //     variables.clone(),
        //     triggers.clone(),
        //     vir_low::Expression::implies(guard.clone(), equalities.into_iter().conjoin()),
        // );
        // // let axiom = vir_low::DomainAxiomDecl::new(
        // //     None,
        // //     format!(
        // //         "inverse_function_definitional_axiom${}",
        // //         self.inverse_function_domain.axioms.len()
        // //     ),
        // //     axiom_body,
        // // );
        // // eprintln!("axiom: {axiom}");
        // // self.inverse_function_domain.axioms.push(axiom);
        // statements.push(vir_low::Statement::assume(axiom_body, position));

        // ```
        // assert forall parameters ::
        //     {inverse$qp$P$index(parameters)}
        //     guard_with_variables_replaced_with_inverse_functions ==>
        //        perm<P>(parameters, v_old) >= p :
        // ```
        // let permission_mask_assert_statement = vir_low::Statement::assert(
        //     vir_low::Expression::forall(
        //         parameters,
        //         vec![vir_low::Trigger::new(permission_mask_assert_trigger_terms)],
        //         vir_low::Expression::implies(
        //             permission_mask_assert_guard,
        //             operations.perm_old_positive(self, parameters_as_arguments)?,
        //         ),
        //     ),
        //     position, // FIXME: use position of expression.permission with proper ErrorCtxt.
        // );
        let permission_mask_assert_statement = vir_low::Statement::assert(
            vir_low::Expression::implies(
                guard,
                operations.perm_old_positive(self, predicate.arguments.clone())?,
            ),
            position, // FIXME: use position of expression.permission with proper ErrorCtxt.
        );
        // eprintln!(
        //     "permission_mask_assert_statement: {}",
        //     permission_mask_assert_statement
        // );
        statements.push(permission_mask_assert_statement);
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
            let expression = self.purify_snap_function_calls_in_expression(
                statements,
                expression,
                Some(expression_evaluation_state_label.to_string()),
                position,
                false,
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
                        PredicatePermissionMaskKind::AliasedWholeDuplicable => {
                            let operations = PermissionMaskOperations::<
                                PermissionMaskKindAliasedDuplicableBool,
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
                        // let guard = self.purify_snap_function_calls_in_expression(
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
                vir_low::Expression::Quantifier(expression) => {
                    if let vir_low::Expression::BinaryOp(vir_low::BinaryOp {
                        op_kind: vir_low::BinaryOpKind::Implies,
                        left: box guard,
                        right: box vir_low::Expression::PredicateAccessPredicate(predicate),
                        ..
                    }) = *expression.body
                    {
                        let guard = self.purify_snap_function_calls_in_expression(
                            statements,
                            guard,
                            Some(expression_evaluation_state_label.to_string()),
                            position,
                            false,
                        )?;
                        self.create_quantifier_variables_remap(&expression.variables)?;
                        eprintln!("guard: {guard}");
                        eprintln!("body: {predicate}");
                        match self.get_predicate_permission_mask_kind(&predicate.name)? {
                            PredicatePermissionMaskKind::AliasedWholeBool
                            | PredicatePermissionMaskKind::AliasedFractionalBool => {
                                let operations = QuantifiedPermissionMaskOperations::<
                                    PermissionMaskKindAliasedBool,
                                >::new(
                                    self,
                                    statements,
                                    &predicate,
                                    Some(expression_evaluation_state_label.to_string()),
                                    position,
                                )?;
                                self.encode_expression_exhale_quantified_predicate(
                                    statements,
                                    expression.variables,
                                    guard,
                                    &predicate,
                                    expression.triggers,
                                    position,
                                    Some(expression_evaluation_state_label.to_string()),
                                    operations,
                                )?
                            }
                            PredicatePermissionMaskKind::AliasedFractionalBoundedPerm => {
                                let operations = QuantifiedPermissionMaskOperations::<
                                    PermissionMaskKindAliasedFractionalBoundedPerm,
                                >::new(
                                    self,
                                    statements,
                                    &predicate,
                                    Some(expression_evaluation_state_label.to_string()),
                                    position,
                                )?;
                                self.encode_expression_exhale_quantified_predicate(
                                    statements,
                                    expression.variables,
                                    guard,
                                    &predicate,
                                    expression.triggers,
                                    position,
                                    Some(expression_evaluation_state_label.to_string()),
                                    operations,
                                )?
                            }
                            PredicatePermissionMaskKind::AliasedWholeDuplicable => {
                                let operations = QuantifiedPermissionMaskOperations::<
                                    PermissionMaskKindAliasedDuplicableBool,
                                >::new(
                                    self,
                                    statements,
                                    &predicate,
                                    Some(expression_evaluation_state_label.to_string()),
                                    position,
                                )?;
                                self.encode_expression_exhale_quantified_predicate(
                                    statements,
                                    expression.variables,
                                    guard,
                                    &predicate,
                                    expression.triggers,
                                    position,
                                    Some(expression_evaluation_state_label.to_string()),
                                    operations,
                                )?
                            }
                        }
                        self.bound_variable_remap_stack.pop();
                    } else {
                        unimplemented!("expression: {:?}", expression);
                    }
                }
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

    fn encode_expression_exhale_quantified_predicate<'a, Kind: PermissionMaskKind>(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        variables: Vec<vir_low::VariableDecl>,
        guard: vir_low::Expression,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        triggers: Vec<vir_low::Trigger>,
        position: vir_low::Position,
        // FIXME: The use of `expression_evaluation_state_label` is probably
        // wrong in both QP and non-QP inhale. Shouldn't arguments be always
        // purified?
        expression_evaluation_state_label: Option<String>,
        operations: QuantifiedPermissionMaskOperations<'a, Kind>,
    ) -> SpannedEncodingResult<()>
    where
        QuantifiedPermissionMaskOperations<'a, Kind>: TQuantifiedPermissionMaskOperations,
    {
        // FIXME: Code duplication with encode_function_precondition_assert_rec_quantified_predicate
        statements.push(vir_low::Statement::comment(format!(
            "exhale-qp-predicate {guard} ==> {predicate}"
        )));
        eprintln!(
            "variables: {}",
            vir_crate::common::display::cjoin(&variables)
        );
        eprintln!("guard: {}", guard);
        eprintln!("predicate: {}", predicate);
        // Generate inverse functions for the variables.
        // ```
        // forall index: Int ::
        //    0 <= index && index < size ==>
        //    inverse$qp$P$index(offset(addr, index), Size$Pair()) == index
        // ```
        // Also construct the necessary parts for the permission mask update quantifier.
        let parameters: Vec<_> = predicate
            .arguments
            .iter()
            .enumerate()
            .map(|(index, argument)| {
                vir_low::VariableDecl::new(format!("_{index}"), argument.get_type().clone())
            })
            .collect();
        let parameters_as_arguments: Vec<_> = parameters
            .clone()
            .into_iter()
            .map(|parameter| parameter.into())
            .collect();
        let mut permission_mask_trigger_terms = Vec::new();
        let mut permission_mask_guard = guard.clone();
        let mut equalities: Vec<vir_low::Expression> = Vec::new();
        for variable in &variables {
            let inverse_function_name = format!(
                "inverse$qp${}${}${}",
                predicate.name,
                variable.name,
                self.inverse_function_domain.functions.len()
            );
            {
                // Declare the inverse function.
                let inverse_function = vir_low::DomainFunctionDecl::new(
                    inverse_function_name.clone(),
                    false,
                    parameters.clone(),
                    variable.ty.clone(),
                );
                let permission_mask_inverse_function_call =
                    vir_low::Expression::domain_function_call(
                        self.inverse_function_domain.name.clone(),
                        inverse_function_name.clone(),
                        parameters_as_arguments.clone(),
                        variable.ty.clone(),
                    );
                permission_mask_guard = permission_mask_guard.replace_place(
                    &variable.clone().into(),
                    &permission_mask_inverse_function_call,
                );
                permission_mask_trigger_terms.push(permission_mask_inverse_function_call);
                self.inverse_function_domain
                    .functions
                    .push(inverse_function);
            }
            {
                // Declare the inverse function definitional equality.
                let inverse_function_call = vir_low::Expression::domain_function_call(
                    self.inverse_function_domain.name.clone(),
                    inverse_function_name,
                    predicate.arguments.clone(),
                    variable.ty.clone(),
                );
                eprintln!("inverse_function: {}", inverse_function_call);
                equalities.push(vir_low::Expression::equals(
                    variable.clone().into(),
                    inverse_function_call,
                ));
            }
        }
        let axiom_body = vir_low::Expression::forall(
            variables.clone(),
            triggers.clone(),
            vir_low::Expression::implies(guard.clone(), equalities.into_iter().conjoin()),
        );
        // let axiom = vir_low::DomainAxiomDecl::new(
        //     None,
        //     format!(
        //         "inverse_function_definitional_axiom${}",
        //         self.inverse_function_domain.axioms.len()
        //     ),
        //     axiom_body,
        // );
        // eprintln!("axiom: {axiom}");
        // self.inverse_function_domain.axioms.push(axiom);
        statements.push(vir_low::Statement::assume(axiom_body, position));

        // ```
        // assert forall parameters ::
        //     {inverse$qp$P$index(parameters)}
        //     guard_with_variables_replaced_with_inverse_functions ==>
        //        perm<P>(parameters, v_old) >= p :
        // ```
        // let permission_mask_assert_statement = vir_low::Statement::assert(
        //     vir_low::Expression::forall(
        //         parameters.clone(),
        //         vec![vir_low::Trigger::new(permission_mask_trigger_terms.clone())],
        //         vir_low::Expression::implies(
        //             permission_mask_guard.clone(),
        //             operations.perm_old_greater_equals(
        //                 self,
        //                 parameters_as_arguments.clone(),
        //                 &predicate.permission,
        //             )?,
        //         ),
        //     ),
        //     position, // FIXME: use position of expression.permission with proper ErrorCtxt.
        // );
        let permission_mask_assert_arguments = self.purify_snap_function_calls_in_expressions(
            statements,
            predicate.arguments.clone(),
            expression_evaluation_state_label.clone(),
            position,
            true,
        )?;
        let permission_mask_assert_statement = vir_low::Statement::assert(
            vir_low::Expression::implies(
                self.purify_snap_function_calls_in_expression(
                    statements,
                    guard.clone(),
                    expression_evaluation_state_label,
                    position,
                    true,
                )?,
                operations.perm_old_greater_equals(
                    self,
                    permission_mask_assert_arguments,
                    &predicate.permission,
                )?,
            ),
            position, // FIXME: use position of expression.permission with proper ErrorCtxt.
        );
        statements.push(permission_mask_assert_statement);

        let perm_new_value = operations.perm_old_sub(
            self,
            parameters_as_arguments.clone(),
            &predicate.permission,
        )?;
        eprintln!("perm_new_value: {}", perm_new_value);
        let perm_new = operations.perm_new(self, parameters_as_arguments.clone())?;
        let perm_old = operations.perm_old(self, parameters_as_arguments.clone())?;
        // Compared to `encode_expression_inhale_predicate`, the setting of the new value and
        // transfering the old values is merged into a single quantifer:
        // ```
        // assume forall parameters ::
        //     {inverse$qp$P$index(parameters)}
        //     perm<P>(parameters, v_new) == (
        //        guard_with_variables_replaced_with_inverse_functions ?
        //        perm<P>(parameters, v_old) + p :
        //        perm<P>(parameters, v_old)
        //     )
        // ```
        let permission_mask_update_statement = vir_low::Statement::assume(
            vir_low::Expression::forall(
                parameters,
                vec![vir_low::Trigger::new(permission_mask_trigger_terms)],
                vir_low::Expression::equals(
                    perm_new,
                    vir_low::Expression::conditional(
                        permission_mask_guard,
                        perm_new_value,
                        perm_old,
                        position,
                    ),
                ),
            ),
            position, // FIXME: use position of expression.permission with proper ErrorCtxt.
        );
        eprintln!(
            "permission_mask_update_statement: {}",
            permission_mask_update_statement
        );
        statements.push(permission_mask_update_statement);
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
            let expression = self.purify_snap_function_calls_in_expression(
                statements,
                expression,
                expression_evaluation_state_label,
                position,
                false,
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
                        PredicatePermissionMaskKind::AliasedWholeDuplicable => {
                            let operations = PermissionMaskOperations::<
                                PermissionMaskKindAliasedDuplicableBool,
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
                        let guard = self.purify_snap_function_calls_in_expression(
                            statements,
                            *expression.left,
                            expression_evaluation_state_label.clone(),
                            position,
                            false,
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
                vir_low::Expression::Quantifier(expression) => {
                    if let vir_low::Expression::BinaryOp(vir_low::BinaryOp {
                        op_kind: vir_low::BinaryOpKind::Implies,
                        left: box guard,
                        right: box vir_low::Expression::PredicateAccessPredicate(mut predicate),
                        ..
                    }) = *expression.body
                    {
                        self.create_quantifier_variables_remap(&expression.variables)?;
                        let guard = self.purify_snap_function_calls_in_expression(
                            statements,
                            guard,
                            expression_evaluation_state_label.clone(),
                            position,
                            false,
                        )?;
                        predicate.arguments = self.purify_snap_function_calls_in_expressions(
                            statements,
                            predicate.arguments,
                            expression_evaluation_state_label.clone(),
                            position,
                            false,
                        )?;
                        eprintln!("guard: {guard}");
                        eprintln!("body: {predicate}");
                        match self.get_predicate_permission_mask_kind(&predicate.name)? {
                            PredicatePermissionMaskKind::AliasedWholeBool
                            | PredicatePermissionMaskKind::AliasedFractionalBool => {
                                let operations = QuantifiedPermissionMaskOperations::<
                                    PermissionMaskKindAliasedBool,
                                >::new(
                                    self,
                                    statements,
                                    &predicate,
                                    expression_evaluation_state_label.clone(),
                                    position,
                                )?;
                                self.encode_expression_inhale_quantified_predicate(
                                    statements,
                                    expression.variables,
                                    guard,
                                    &predicate,
                                    expression.triggers,
                                    position,
                                    expression_evaluation_state_label,
                                    operations,
                                )?
                            }
                            PredicatePermissionMaskKind::AliasedFractionalBoundedPerm => {
                                let operations = QuantifiedPermissionMaskOperations::<
                                    PermissionMaskKindAliasedFractionalBoundedPerm,
                                >::new(
                                    self,
                                    statements,
                                    &predicate,
                                    expression_evaluation_state_label.clone(),
                                    position,
                                )?;
                                self.encode_expression_inhale_quantified_predicate(
                                    statements,
                                    expression.variables,
                                    guard,
                                    &predicate,
                                    expression.triggers,
                                    position,
                                    expression_evaluation_state_label,
                                    operations,
                                )?
                            }
                            PredicatePermissionMaskKind::AliasedWholeDuplicable => {
                                let operations = QuantifiedPermissionMaskOperations::<
                                    PermissionMaskKindAliasedDuplicableBool,
                                >::new(
                                    self,
                                    statements,
                                    &predicate,
                                    expression_evaluation_state_label.clone(),
                                    position,
                                )?;
                                self.encode_expression_inhale_quantified_predicate(
                                    statements,
                                    expression.variables,
                                    guard,
                                    &predicate,
                                    expression.triggers,
                                    position,
                                    expression_evaluation_state_label,
                                    operations,
                                )?
                            }
                        }
                        self.bound_variable_remap_stack.pop();
                    } else {
                        unimplemented!("expression: {:?}", expression);
                    }
                }
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
        // FIXME: The use of `expression_evaluation_state_label` is probably
        // wrong in both QP and non-QP inhale. Shouldn't arguments be always
        // purified?
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

    fn encode_expression_inhale_quantified_predicate<'a, Kind: PermissionMaskKind>(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        variables: Vec<vir_low::VariableDecl>,
        guard: vir_low::Expression,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        triggers: Vec<vir_low::Trigger>,
        position: vir_low::Position,
        // FIXME: The use of `expression_evaluation_state_label` is probably
        // wrong in both QP and non-QP inhale. Shouldn't arguments be always
        // purified?
        expression_evaluation_state_label: Option<String>,
        operations: QuantifiedPermissionMaskOperations<'a, Kind>,
    ) -> SpannedEncodingResult<()>
    where
        QuantifiedPermissionMaskOperations<'a, Kind>: TQuantifiedPermissionMaskOperations,
    {
        // FIXME: Code duplication with encode_function_precondition_assert_rec_quantified_predicate
        statements.push(vir_low::Statement::comment(format!(
            "inhale-qp-predicate {guard} ==> {predicate}"
        )));
        eprintln!(
            "variables: {}",
            vir_crate::common::display::cjoin(&variables)
        );
        eprintln!("guard: {}", guard);
        eprintln!("predicate: {}", predicate);
        // let guard = self.purify_snap_function_calls_in_expression(
        //     statements,
        //     guard,
        //     expression_evaluation_state_label,
        //     position,
        //     true,
        // )?;
        if operations.can_assume_old_permission_is_none(&predicate.permission) {
            statements.push(vir_low::Statement::assume(
                vir_low::Expression::forall(
                    variables.clone(),
                    triggers.clone(),
                    vir_low::Expression::implies(
                        guard.clone(),
                        operations.perm_old_equal_none(self, predicate.arguments.clone())?,
                    ),
                ),
                position, // FIXME: use position of expression.permission with proper ErrorCtxt.
            ));
        }
        // Generate inverse functions for the variables.
        // ```
        // forall index: Int ::
        //    0 <= index && index < size ==>
        //    inverse$qp$P$index(offset(addr, index), Size$Pair()) == index
        // ```
        // Also construct the necessary parts for the permission mask update quantifier.
        let parameters: Vec<_> = predicate
            .arguments
            .iter()
            .enumerate()
            .map(|(index, argument)| {
                vir_low::VariableDecl::new(format!("_{index}"), argument.get_type().clone())
            })
            .collect();
        let parameters_as_arguments: Vec<_> = parameters
            .clone()
            .into_iter()
            .map(|parameter| parameter.into())
            .collect();
        let mut permission_mask_update_trigger_terms = Vec::new();
        let mut permission_mask_update_guard = guard.clone();
        let mut equalities: Vec<vir_low::Expression> = Vec::new();
        for variable in &variables {
            let inverse_function_name = format!(
                "inverse$qp${}${}${}",
                predicate.name,
                variable.name,
                self.inverse_function_domain.functions.len()
            );
            {
                // Declare the inverse function.
                let inverse_function = vir_low::DomainFunctionDecl::new(
                    inverse_function_name.clone(),
                    false,
                    parameters.clone(),
                    variable.ty.clone(),
                );
                let permission_mask_update_inverse_function_call =
                    vir_low::Expression::domain_function_call(
                        self.inverse_function_domain.name.clone(),
                        inverse_function_name.clone(),
                        parameters_as_arguments.clone(),
                        variable.ty.clone(),
                    );
                permission_mask_update_guard = permission_mask_update_guard.replace_place(
                    &variable.clone().into(),
                    &permission_mask_update_inverse_function_call,
                );
                permission_mask_update_trigger_terms
                    .push(permission_mask_update_inverse_function_call);
                self.inverse_function_domain
                    .functions
                    .push(inverse_function);
            }
            {
                // Declare the inverse function definitional equality.
                let inverse_function_call = vir_low::Expression::domain_function_call(
                    self.inverse_function_domain.name.clone(),
                    inverse_function_name,
                    predicate.arguments.clone(),
                    variable.ty.clone(),
                );
                eprintln!("inverse_function: {}", inverse_function_call);
                equalities.push(vir_low::Expression::equals(
                    variable.clone().into(),
                    inverse_function_call,
                ));
            }
        }
        let axiom_body = vir_low::Expression::forall(
            variables.clone(),
            triggers.clone(),
            vir_low::Expression::implies(guard.clone(), equalities.into_iter().conjoin()),
        );
        // let axiom = vir_low::DomainAxiomDecl::new(
        //     None,
        //     format!(
        //         "inverse_function_definitional_axiom${}",
        //         self.inverse_function_domain.axioms.len()
        //     ),
        //     axiom_body,
        // );
        // eprintln!("axiom: {axiom}");
        // self.inverse_function_domain.axioms.push(axiom);
        statements.push(vir_low::Statement::assume(axiom_body, position));

        let perm_new_value = operations.perm_old_add(
            self,
            parameters_as_arguments.clone(),
            &predicate.permission,
        )?;
        eprintln!("perm_new_value: {}", perm_new_value);
        let perm_new = operations.perm_new(self, parameters_as_arguments.clone())?;
        let perm_old = operations.perm_old(self, parameters_as_arguments.clone())?;
        // Compared to `encode_expression_inhale_predicate`, the setting of the new value and
        // transfering the old values is merged into a single quantifer:
        // ```
        // assume forall parameters ::
        //     {inverse$qp$P$index(parameters)}
        //     perm<P>(parameters, v_new) == (
        //        guard_with_variables_replaced_with_inverse_functions ?
        //        perm<P>(parameters, v_old) + p :
        //        perm<P>(parameters, v_old)
        //     )
        // ```
        let permission_mask_update_statement = vir_low::Statement::assume(
            vir_low::Expression::forall(
                parameters,
                vec![vir_low::Trigger::new(permission_mask_update_trigger_terms)],
                vir_low::Expression::equals(
                    perm_new,
                    vir_low::Expression::conditional(
                        permission_mask_update_guard,
                        perm_new_value,
                        perm_old,
                        position,
                    ),
                ),
            ),
            position, // FIXME: use position of expression.permission with proper ErrorCtxt.
        );
        eprintln!(
            "permission_mask_update_statement: {}",
            permission_mask_update_statement
        );
        statements.push(permission_mask_update_statement);
        Ok(())
    }
}
