mod operations;

use super::HeapEncoder;
use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, ExpressionIterator, QuantifierHelpers},
    low::{self as vir_low},
};

pub(super) use self::operations::{
    PermissionMaskKind, PermissionMaskKindAliasedBool,
    PermissionMaskKindAliasedFractionalBoundedPerm, PermissionMaskOperations,
    TPermissionMaskOperations,
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum PredicatePermissionMaskKind {
    /// The permission amounts can be either full or none.
    AliasedWholeBool,
    /// The permission amounts can be fractional, but we are always guaranteed
    /// to operate on the same amount. Therefore, we do not need to perform
    /// arithmetic operations on permissions and can use a boolean permission
    /// mask with a third parameter that specifies the permission amount that we
    /// are currently tracking.
    AliasedFractionalBool,
    /// The permission amounts can be fractional and we need to perform
    /// arithmetic operations on them. However, the permission amount is bounded
    /// by `write` and, therefore, when inhaling `write` we can assume that the
    /// current amount is `none`.
    AliasedFractionalBoundedPerm,
    /// The permission amounts are natural numbers.
    AliasedWholeNat,
}

impl<'p, 'v: 'p, 'tcx: 'v> HeapEncoder<'p, 'v, 'tcx> {
    fn perm_version_type(&self) -> vir_low::Type {
        vir_low::Type::domain("PermVersion".to_string())
    }

    fn mask_function_return_type(&self, kind: PredicatePermissionMaskKind) -> vir_low::Type {
        match kind {
            PredicatePermissionMaskKind::AliasedWholeBool
            | PredicatePermissionMaskKind::AliasedFractionalBool => vir_low::Type::Bool,
            PredicatePermissionMaskKind::AliasedWholeNat
            | PredicatePermissionMaskKind::AliasedFractionalBoundedPerm => vir_low::Type::Perm,
        }
    }

    fn no_permission(&self, kind: PredicatePermissionMaskKind) -> vir_low::Expression {
        match kind {
            PredicatePermissionMaskKind::AliasedWholeBool
            | PredicatePermissionMaskKind::AliasedFractionalBool => false.into(),
            PredicatePermissionMaskKind::AliasedWholeNat
            | PredicatePermissionMaskKind::AliasedFractionalBoundedPerm => {
                vir_low::Expression::no_permission()
            }
        }
    }

    fn permission_amount_parameter(
        &self,
        kind: PredicatePermissionMaskKind,
    ) -> Option<vir_low::VariableDecl> {
        match kind {
            PredicatePermissionMaskKind::AliasedWholeNat
            | PredicatePermissionMaskKind::AliasedFractionalBool => Some(
                vir_low::VariableDecl::new("permission_amount", vir_low::Type::Perm),
            ),
            PredicatePermissionMaskKind::AliasedWholeBool
            | PredicatePermissionMaskKind::AliasedFractionalBoundedPerm => None,
        }
    }

    fn permission_mask_function_name(&self, predicate_name: &str) -> String {
        format!("perm${predicate_name}")
    }

    pub(super) fn get_current_permission_mask_for(
        &mut self,
        predicate_name: &str,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let variable_name = self.permission_mask_names.get(predicate_name).unwrap();
        let version = self.ssa_state.current_variable_version(variable_name);
        let ty = self.perm_version_type();
        Ok(self
            .new_variables
            .create_variable(variable_name, ty, version)?
            .into())
    }

    pub(super) fn get_new_permission_mask_for(
        &mut self,
        predicate_name: &str,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let variable_name = self.permission_mask_names.get(predicate_name).unwrap();
        let ty = self.perm_version_type();
        let version = self
            .ssa_state
            .new_variable_version(variable_name, &ty, position);
        Ok(self
            .new_variables
            .create_variable(variable_name, ty, version)?
            .into())
    }

    pub(super) fn permission_mask_call(
        &mut self,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        mut arguments: Vec<vir_low::Expression>,
        permission_mask_version: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let perm_function_name = self.permission_mask_function_name(&predicate.name);
        arguments.push(permission_mask_version);
        let kind = self.get_predicate_permission_mask_kind(&predicate.name)?;
        if kind == PredicatePermissionMaskKind::AliasedFractionalBool {
            arguments.push((*predicate.permission).clone());
        }
        let return_type = self.mask_function_return_type(kind);
        Ok(vir_low::Expression::domain_function_call(
            "PermFunctions",
            perm_function_name,
            arguments,
            return_type,
        ))
    }

    pub(super) fn permission_mask_call_for_predicate_use(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        permission_mask: vir_low::Expression,
        expression_evaluation_state_label: Option<String>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let arguments = self.purify_predicate_arguments(
            statements,
            predicate,
            expression_evaluation_state_label,
            position,
        )?;
        self.permission_mask_call(predicate, arguments, permission_mask)
    }

    pub(super) fn permission_mask_call_for_predicate_def(
        &mut self,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        permission_mask: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let arguments = self.get_predicate_parameters_as_arguments(&predicate.name)?;
        self.permission_mask_call(predicate, arguments, permission_mask)
    }

    pub(super) fn positive_permission_mask_call_for_predicate_def(
        &mut self,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        permission_mask: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let perm_call = self.permission_mask_call_for_predicate_def(predicate, permission_mask)?;
        let kind = self.get_predicate_permission_mask_kind(&predicate.name)?;
        let positivity_check = match kind {
            PredicatePermissionMaskKind::AliasedWholeBool
            | PredicatePermissionMaskKind::AliasedFractionalBool => perm_call,
            PredicatePermissionMaskKind::AliasedFractionalBoundedPerm => {
                vir_low::Expression::greater_than(perm_call, vir_low::Expression::no_permission())
            }
            PredicatePermissionMaskKind::AliasedWholeNat => unimplemented!(),
        };
        Ok(positivity_check)
    }

    pub(super) fn encode_perm_unchanged_quantifier(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        old_permission_mask_version: vir_low::Expression,
        new_permission_mask_version: vir_low::Expression,
        position: vir_low::Position,
        expression_evaluation_state_label: Option<String>,
        perm_new_value: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        let perm_new =
            self.permission_mask_call_for_predicate_def(predicate, new_permission_mask_version)?;
        let perm_old =
            self.permission_mask_call_for_predicate_def(predicate, old_permission_mask_version)?;
        let predicate_parameters = self.get_predicate_parameters(&predicate.name).to_owned();
        let predicate_arguments = self.get_predicate_parameters_as_arguments(&predicate.name)?;
        let arguments = self.purify_predicate_arguments(
            statements,
            predicate,
            expression_evaluation_state_label,
            position,
        )?;
        let triggers = vec![vir_low::Trigger::new(vec![perm_new.clone()])];
        let guard = predicate_arguments
            .into_iter()
            .zip(arguments)
            .map(|(parameter, argument)| vir_low::Expression::equals(parameter, argument))
            .conjoin();
        let body = vir_low::Expression::equals(
            perm_new,
            vir_low::Expression::conditional_no_pos(guard, perm_new_value, perm_old),
        );
        statements.push(vir_low::Statement::assume(
            vir_low::Expression::forall(predicate_parameters, triggers, body),
            position,
        ));
        Ok(())
    }

    pub(super) fn generate_permission_mask_domains(
        &self,
        domains: &mut Vec<vir_low::DomainDecl>,
    ) -> SpannedEncodingResult<()> {
        let perm_version_domain =
            vir_low::DomainDecl::new("PermVersion", Vec::new(), Vec::new(), Vec::new());
        domains.push(perm_version_domain);
        let mut functions = Vec::new();
        let mut axioms = Vec::new();
        for predicate in self.predicates.iter_decls() {
            let mut parameters = predicate.parameters.clone();
            parameters.push(vir_low::VariableDecl::new(
                "version",
                self.perm_version_type(),
            ));
            let function_name = self.permission_mask_function_name(&predicate.name);
            let kind = self.get_predicate_permission_mask_kind(&predicate.name)?;
            parameters.extend(self.permission_amount_parameter(kind));
            let return_type = self.mask_function_return_type(kind);
            let function = vir_low::DomainFunctionDecl::new(
                function_name.clone(),
                false,
                parameters.clone(),
                return_type,
            );
            functions.push(function);
            if matches!(
                kind,
                PredicatePermissionMaskKind::AliasedFractionalBoundedPerm
            ) {
                let function_call = vir_low::Expression::domain_func_app_no_pos(
                    "PermFunctions".to_string(),
                    function_name.clone(),
                    parameters
                        .clone()
                        .into_iter()
                        .map(|parameter| parameter.into())
                        .collect(),
                    parameters.clone(),
                    vir_low::Type::Perm,
                );
                use vir_low::macros::*;
                let body = vir_low::Expression::forall(
                    parameters,
                    vec![vir_low::Trigger::new(vec![function_call.clone()])],
                    expr! {
                        ([vir_low::Expression::no_permission()] <= [function_call.clone()]) &&
                        ([function_call] <= [vir_low::Expression::full_permission()])
                    },
                );
                let axiom =
                    vir_low::DomainAxiomDecl::new(None, format!("{function_name}$bounds"), body);
                axioms.push(axiom);
            }
        }
        let perm_domain = vir_low::DomainDecl::new("PermFunctions", functions, axioms, Vec::new());
        domains.push(perm_domain);
        Ok(())
    }

    pub(super) fn generate_init_permissions_to_zero_internal(
        &mut self,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Vec<vir_low::Statement>> {
        assert!(!position.is_default());
        let mut statements = Vec::new();
        for predicate in self.predicates.iter_decls() {
            let initial_permission_mask_name =
                self.permission_mask_names.get(&predicate.name).unwrap();
            let initial_permission_mask_version = self
                .ssa_state
                .initial_variable_version(initial_permission_mask_name);
            let initial_permission_mask_ty = self.perm_version_type();
            let initial_permission_mask: vir_low::Expression = self
                .new_variables
                .create_variable(
                    initial_permission_mask_name,
                    initial_permission_mask_ty,
                    initial_permission_mask_version,
                )?
                .into();
            let kind = self.get_predicate_permission_mask_kind(&predicate.name)?;
            let mut arguments: Vec<_> = predicate
                .parameters
                .iter()
                .map(|parameter| parameter.clone().into())
                .collect();
            arguments.push(initial_permission_mask.clone());
            arguments.extend(
                self.permission_amount_parameter(kind)
                    .map(|parameter| parameter.into()),
            );
            let perm_function_name = self.permission_mask_function_name(&predicate.name);
            let return_type = self.mask_function_return_type(kind);
            let perm = vir_low::Expression::domain_function_call(
                "PermFunctions",
                perm_function_name.clone(),
                arguments,
                return_type,
            );
            let no_permission = self.no_permission(kind);
            let triggers = vec![vir_low::Trigger::new(vec![perm.clone()])];
            let body = vir_low::Expression::equals(perm, no_permission);
            let mut parameters = predicate.parameters.clone();
            parameters.extend(self.permission_amount_parameter(kind));
            statements.push(vir_low::Statement::assume(
                vir_low::Expression::forall(parameters, triggers, body),
                position,
            ));
        }
        Ok(statements)
    }
}
