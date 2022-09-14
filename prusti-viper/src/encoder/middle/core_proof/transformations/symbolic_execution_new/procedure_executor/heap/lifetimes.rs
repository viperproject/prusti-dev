use super::super::constraints::BlockConstraints;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::symbolic_execution_new::{
        block_builder::BlockBuilder, procedure_executor::constraints::ConstraintsMergeReport,
    },
};
use log::{debug, error};
use prusti_common::config;
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low},
};

#[derive(Default, Clone)]
pub(super) struct LifetimeTokens<const IS_DEAD: bool> {
    // FIXME: This field should be private.
    pub(super) token_permission_amounts: BTreeMap<String, vir_low::Expression>,
}

impl<const IS_DEAD: bool> std::fmt::Display for LifetimeTokens<IS_DEAD> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (lifetime, permission_amount) in &self.token_permission_amounts {
            writeln!(f, "{}: {}", lifetime, permission_amount)?;
        }
        Ok(())
    }
}

impl<const IS_DEAD: bool> LifetimeTokens<IS_DEAD> {
    pub(super) fn inhale(
        &mut self,
        mut predicate: vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
        constraints: &BlockConstraints,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        assert_eq!(predicate.arguments.len(), 1);
        let Some(vir_low::Expression::Local(local)) = predicate.arguments.pop() else {
            unimplemented!("TODO: A proper error message.");
        };
        let mut lifetime = local.variable.name;
        if let Some(cannonical_lifetime) =
            constraints.resolve_cannonical_lifetime_name(&lifetime)?
        {
            lifetime = cannonical_lifetime.to_string();
        }
        let permission_amount_is_non_negative = vir_low::Statement::assert(
            vir_low::Expression::greater_equals(
                (*predicate.permission).clone(),
                vir_low::Expression::no_permission(),
            ),
            position,
        );
        if let Some(amount) = self.token_permission_amounts.get_mut(&lifetime) {
            if IS_DEAD {
                // Since DeadLifetimeToken is duplicable, we only track whether
                // we have permission or not.
            } else {
                *amount = vir_low::Expression::perm_binary_op(
                    vir_low::PermBinaryOpKind::Add,
                    amount.clone(),
                    *predicate.permission,
                    position,
                )
                .simplify_perm();
            }
        } else {
            self.token_permission_amounts
                .insert(lifetime, *predicate.permission);
        }
        block_builder.add_statement(permission_amount_is_non_negative)?;
        Ok(())
    }

    pub(super) fn exhale(
        &mut self,
        mut predicate: vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
        constraints: &BlockConstraints,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        debug!("  Exhaling predicate: {predicate}");
        assert_eq!(predicate.arguments.len(), 1);
        let Some(vir_low::Expression::Local(local)) = predicate.arguments.pop() else {
            unimplemented!("TODO: A proper error message.");
        };
        let mut lifetime = local.variable.name.clone();
        if let Some(cannonical_lifetime) =
            constraints.resolve_cannonical_lifetime_name(&lifetime)?
        {
            lifetime = cannonical_lifetime.to_string();
        }
        if let Some(mut amount) = self.token_permission_amounts.remove(&lifetime) {
            if IS_DEAD {
                // Since DeadLifetimeToken is duplicable, the exhale only
                // asserts that we have the permission.
            } else {
                amount = vir_low::Expression::perm_binary_op(
                    vir_low::PermBinaryOpKind::Sub,
                    amount,
                    *predicate.permission,
                    position,
                );
                amount = amount.simplify_perm();
            }
            if !amount.is_no_permission() {
                self.token_permission_amounts
                    .insert(lifetime, amount.clone());
                let permission_amount_is_non_negative = vir_low::Statement::assert(
                    vir_low::Expression::greater_equals(
                        amount,
                        vir_low::Expression::no_permission(),
                    ),
                    position,
                );
                block_builder.add_statement(permission_amount_is_non_negative)?;
            };
        } else if config::panic_on_failed_exhale() {
            panic!("failed to exhale: {predicate}\n{self}");
        } else {
            // It could be that the permission tracking is not precise enough. Emit a conditional exhale.
            let mut sum = vir_low::Expression::no_permission();
            for (chunk_lifetime, amount) in &self.token_permission_amounts {
                sum = vir_low::Expression::perm_binary_op_no_pos(
                    vir_low::PermBinaryOpKind::Add,
                    sum,
                    vir_low::Expression::conditional_no_pos(
                        vir_low::Expression::equals(
                            local.variable.clone().into(),
                            vir_low::VariableDecl::new(
                                chunk_lifetime.clone(),
                                local.variable.ty.clone(),
                            )
                            .into(),
                        ),
                        amount.clone(),
                        vir_low::Expression::no_permission(),
                    ),
                );
            }
            block_builder.add_statement(vir_low::Statement::comment(format!(
                "Failed to syntactically exhale: {predicate} {lifetime} at {position}"
            )))?;
            block_builder.add_statement(
                vir_low::Statement::assert_no_pos(vir_low::Expression::greater_equals(
                    sum,
                    *predicate.permission,
                ))
                .set_default_position(position),
            )?;
        }
        Ok(())
    }

    pub(super) fn merge(
        &mut self,
        other: &Self,
        constraints_merge_report: &ConstraintsMergeReport,
    ) -> SpannedEncodingResult<()> {
        for (mut lifetime, amount) in std::mem::take(&mut self.token_permission_amounts) {
            let other_amount = if let Some(other_amount) =
                other.token_permission_amounts.get(&lifetime)
            {
                other_amount
            } else {
                if let Some(cannonical_self) =
                    constraints_merge_report.resolve_new_self_cannonical_lifetime_name(&lifetime)
                {
                    lifetime = cannonical_self.clone();
                }
                if let Some(other_lifetime) =
                    constraints_merge_report.resolve_old_other_cannonical_lifetime_name(&lifetime)
                {
                    if let Some(other_amount) = other.token_permission_amounts.get(other_lifetime) {
                        other_amount
                    } else {
                        // This can happen if the reference was not closed on
                        // some (potentially unreachable) trace.
                        unimplemented!("{other_lifetime}\n{self}");
                        // // Did not find the lifetime in the other block, leak it.
                        // continue;
                    }
                } else {
                    // This can happen if the reference was not closed on some
                    // (potentially unreachable) trace.
                    unimplemented!("{lifetime}\nself:\n{self}other:\n{other}");
                    // // Did not find the lifetime in the other block, leak it.
                    // continue;
                }
            };
            assert_eq!(&amount, other_amount);
            self.token_permission_amounts.insert(lifetime, amount);
        }
        for (lifetime, amount) in &other.token_permission_amounts {
            let self_amount = if let Some(self_amount) = self.token_permission_amounts.get(lifetime)
            {
                self_amount
            } else {
                if let Some(self_lifetime) =
                    constraints_merge_report.resolve_new_other_cannonical_lifetime_name(lifetime)
                {
                    if let Some(self_amount) = self.token_permission_amounts.get(self_lifetime) {
                        self_amount
                    } else {
                        // This can happen if the reference was not closed on some
                        // (potentially unreachable) trace.
                        unimplemented!("{self_lifetime}\n{self}");
                        // // Did not find the lifetime in the other block, leak it.
                        // continue;
                    }
                } else {
                    // This can happen if the reference was not closed on some
                    // (potentially unreachable) trace.
                    unimplemented!("{lifetime}\n{self}");
                    // // Did not find the lifetime in the other block, leak it.
                    // continue;
                }
            };
            assert_eq!(self_amount, amount);
        }
        Ok(())
    }

    pub(super) fn leak_check(&self) -> SpannedEncodingResult<()> {
        for (lifetime, amount) in &self.token_permission_amounts {
            error!(
                "ERROR: Lifetime token {} was not exhaled. Its amount is {}.",
                lifetime, amount
            );
        }
        assert!(self.token_permission_amounts.is_empty());
        Ok(())
    }

    // pub(super) fn get_dead_lifetime_equality_classes(
    //     &self,
    //     constraints: &BlockConstraints,
    // ) -> SpannedEncodingResult<BTreeMap<String, BTreeSet<String>>> {
    //     let mut map = BTreeMap::new();
    //     for lifetime in self.token_permission_amounts.keys() {
    //         map.insert(lifetime.clone(), constraints.get_equal_lifetimes(lifetime)?);
    //     }
    //     Ok(map)
    // }

    // pub(super) fn remap_lifetimes(
    //     &mut self,
    //     mut remaps: BTreeMap<String, String>,
    // ) -> SpannedEncodingResult<()> {
    //     for (lifetime, amount) in std::mem::take(&mut self.token_permission_amounts) {
    //         let new_lifetime = remaps.remove(&lifetime).unwrap();
    //         assert!(self
    //             .token_permission_amounts
    //             .insert(new_lifetime, amount)
    //             .is_none());
    //     }
    //     Ok(())
    // }
}
