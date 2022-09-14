use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::symbolic_execution::egg::EGraphState,
};
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low},
};

#[derive(Default)]
pub(super) struct LifetimeTokens {
    permission_variables: Vec<PermissionVariable>,
}

impl LifetimeTokens {
    pub(super) fn into_variables(self) -> Vec<vir_low::VariableDecl> {
        let mut variables = Vec::new();
        for permission_variable in self.permission_variables {
            for version in 0..permission_variable.permission_variable_version + 1 {
                variables.push(permission_variable.create_variable(version));
            }
        }
        variables
    }

    fn find_permission_variable(
        &mut self,
        solver: &EGraphState,
        lifetime: &vir_low::Expression,
    ) -> SpannedEncodingResult<Option<&mut PermissionVariable>> {
        for permission_variable in &mut self.permission_variables {
            if solver.is_equal(&permission_variable.lifetime, lifetime)? {
                return Ok(Some(permission_variable));
            }
        }
        Ok(None)
    }

    pub(super) fn inhale_predicate(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        solver: &EGraphState,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        assert_eq!(predicate.arguments.len(), 1);
        if let Some(permission_variable) =
            self.find_permission_variable(solver, &predicate.arguments[0])?
        {
            let current_permission_amount_variable =
                permission_variable.current_permission_amount_variable();
            let new_permission_amount_variable =
                permission_variable.new_permission_amount_variable();
            statements.push(vir_low::Statement::assume(
                vir_low::Expression::equals(
                    new_permission_amount_variable.into(),
                    vir_low::Expression::perm_binary_op_no_pos(
                        vir_low::PermBinaryOpKind::Add,
                        current_permission_amount_variable.into(),
                        (*predicate.permission).clone(),
                    ),
                )
                .set_default_position(position),
                position,
            ));
        } else {
            let permission_variable = PermissionVariable {
                lifetime: predicate.arguments[0].clone(),
                permission_variable_name: format!(
                    "lifetime_token${}",
                    self.permission_variables.len()
                ),
                permission_variable_version: 0,
            };
            let new_permission_amount_variable =
                permission_variable.current_permission_amount_variable();
            self.permission_variables.push(permission_variable);
            statements.push(vir_low::Statement::assume(
                vir_low::Expression::equals(
                    new_permission_amount_variable.into(),
                    (*predicate.permission).clone(),
                )
                .set_default_position(position),
                position,
            ));
        }
        Ok(())
    }

    pub(super) fn exhale_predicate(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        solver: &EGraphState,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        assert_eq!(predicate.arguments.len(), 1);
        if let Some(permission_variable) =
            self.find_permission_variable(solver, &predicate.arguments[0])?
        {
            let current_permission_amount_variable =
                permission_variable.current_permission_amount_variable();
            let new_permission_amount_variable =
                permission_variable.new_permission_amount_variable();
            statements.push(vir_low::Statement::assert(
                vir_low::Expression::greater_equals(
                    current_permission_amount_variable.clone().into(),
                    (*predicate.permission).clone(),
                )
                .set_default_position(position),
                position,
            ));
            statements.push(vir_low::Statement::assume(
                vir_low::Expression::equals(
                    new_permission_amount_variable.into(),
                    vir_low::Expression::perm_binary_op_no_pos(
                        vir_low::PermBinaryOpKind::Sub,
                        current_permission_amount_variable.into(),
                        (*predicate.permission).clone(),
                    ),
                )
                .set_default_position(position),
                position,
            ));
        } else {
            unreachable!("Exhaling a predicate that was not inhaled before: {predicate}");
        }
        Ok(())
    }
}

struct PermissionVariable {
    /// An expression that indicates the lifetime that is mapped to this
    /// variable.
    lifetime: vir_low::Expression,
    /// The name of the variable used to track the permission amount of this
    /// lifetime.
    permission_variable_name: String,
    /// The SSA version of the permission variable.
    permission_variable_version: u32,
}

impl PermissionVariable {
    fn create_variable(&self, version: u32) -> vir_low::VariableDecl {
        let variable_name = format!("{}${}", self.permission_variable_name, version);
        vir_low::VariableDecl::new(variable_name, vir_low::Type::Perm)
    }

    fn current_permission_amount_variable(&self) -> vir_low::VariableDecl {
        self.create_variable(self.permission_variable_version)
    }

    fn new_permission_amount_variable(&mut self) -> vir_low::VariableDecl {
        self.permission_variable_version += 1;
        self.create_variable(self.permission_variable_version)
    }
}
