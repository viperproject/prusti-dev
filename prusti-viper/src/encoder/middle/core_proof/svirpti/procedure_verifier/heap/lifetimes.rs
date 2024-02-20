use super::super::{
    super::{
        super::transformations::{
            encoder_context::EncoderContext, symbolic_execution_new::ProgramContext,
        },
        smt::{SmtSolver, Sort2SmtWrap},
        VerificationResult, Verifier,
    },
    ProcedureExecutor,
};
use crate::encoder::errors::SpannedEncodingResult;
use log::{debug, error};
use prusti_common::config;
use std::collections::BTreeMap;
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low},
};

#[derive(Default, Clone, Debug)]
pub(in super::super::super::super) struct LifetimeTokens {
    /// Map from variables identifying tokens to variables tracking permission
    /// amounts.
    tokens: BTreeMap<String, usize>,
}

fn permission_variable(id: usize) -> SpannedEncodingResult<vir_low::VariableDecl> {
    let name = format!("lifetime_token_permission${}", id);
    let variable = vir_low::VariableDecl::new(name, vir_low::Type::Perm);
    Ok(variable)
}

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn execute_inhale_lifetime_token(
        &mut self,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        assert_eq!(predicate.arguments.len(), 1);
        let Some(vir_low::Expression::Local(local)) = predicate.arguments.get(0) else {
            unimplemented!("TODO: A proper error message.");
        };
        let permission_amount_is_non_negative = vir_low::Expression::greater_equals(
            (*predicate.permission).clone(),
            vir_low::Expression::no_permission(),
        );
        self.assert(permission_amount_is_non_negative, position)?;
        let new_permission_id = self.generate_fresh_id();
        let new_permission_variable = permission_variable(new_permission_id)?;
        self.declare_variable(&new_permission_variable)?;
        let frame = self.current_frame_mut();
        if let Some(current_permission_id) = frame
            .heap_mut()
            .lifetime_tokens
            .tokens
            .get_mut(&local.variable.name)
        {
            let current_permission_variable = permission_variable(*current_permission_id)?;
            *current_permission_id = new_permission_id;
            let set_new_value = vir_low::Expression::equals(
                new_permission_variable.into(),
                vir_low::Expression::perm_binary_op(
                    vir_low::PermBinaryOpKind::Add,
                    current_permission_variable.clone().into(),
                    (*predicate.permission).clone(),
                    position,
                ),
            );
            self.assume(&set_new_value)?;
        } else {
            frame
                .heap_mut()
                .lifetime_tokens
                .tokens
                .insert(local.variable.name.clone(), new_permission_id);
            let set_new_value = vir_low::Expression::equals(
                new_permission_variable.into(),
                (*predicate.permission).clone(),
            );
            self.assume(&set_new_value)?;
        }
        Ok(())
    }

    pub(super) fn execute_exhale_lifetime_token(
        &mut self,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        assert_eq!(predicate.arguments.len(), 1);
        let Some(vir_low::Expression::Local(local)) = predicate.arguments.get(0) else {
            unimplemented!("TODO: A proper error message.");
        };
        let permission_amount_is_non_negative = vir_low::Expression::greater_equals(
            (*predicate.permission).clone(),
            vir_low::Expression::no_permission(),
        );
        self.assert(permission_amount_is_non_negative, position)?;
        let new_permission_id = self.generate_fresh_id();
        let new_permission_variable = permission_variable(new_permission_id)?;
        self.declare_variable(&new_permission_variable)?;
        let frame = self.current_frame_mut();
        if let Some(current_permission_id) = frame
            .heap_mut()
            .lifetime_tokens
            .tokens
            .get_mut(&local.variable.name)
        {
            let current_permission_variable = permission_variable(*current_permission_id)?;
            *current_permission_id = new_permission_id;
            let set_new_value = vir_low::Expression::equals(
                new_permission_variable.clone().into(),
                vir_low::Expression::perm_binary_op(
                    vir_low::PermBinaryOpKind::Sub,
                    current_permission_variable.clone().into(),
                    (*predicate.permission).clone(),
                    position,
                ),
            );
            self.assume(&set_new_value)?;
            let new_permission_amount_is_non_negative = vir_low::Expression::greater_equals(
                new_permission_variable.into(),
                vir_low::Expression::no_permission(),
            );
            self.assert(new_permission_amount_is_non_negative, position)?;
        } else {
            unimplemented!("TODO: Report a verification error.");
        }
        Ok(())
    }
}
