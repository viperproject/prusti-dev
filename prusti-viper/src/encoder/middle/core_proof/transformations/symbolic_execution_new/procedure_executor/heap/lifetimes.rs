use super::super::constraints::BlockConstraints;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::symbolic_execution_new::{
        block_builder::BlockBuilder, procedure_executor::constraints::ConstraintsMergeReport,
    },
};
use log::{debug, error};
use prusti_common::config;
use std::collections::BTreeMap;
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low},
};

#[derive(Default, Clone)]
pub(in super::super::super::super) struct LifetimeTokens<const IS_DEAD: bool> {
    tokens: BTreeMap<String, LifetimeToken>,
}

#[derive(Clone, Debug)]
struct LifetimeVariable {
    name: String,
    version: u32,
}

impl From<String> for LifetimeVariable {
    fn from(name_with_version: String) -> Self {
        // FIXME: This is a hack. We should use proper versioned variables. The
        // version is the number after the last `$`.
        let mut split = name_with_version.rsplitn(2, '$');
        let part = split.next().unwrap();
        let version = part.parse::<u32>().unwrap();
        let part = split.next().unwrap();
        let name = part.to_string();
        Self { name, version }
    }
}

impl std::fmt::Display for LifetimeVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{name}${version}",
            name = self.name,
            version = self.version
        )
    }
}

#[derive(Clone, Debug)]
struct LifetimeToken {
    latest_variable_version: u32,
    permission_amount: vir_low::Expression,
}

impl std::fmt::Display for LifetimeToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{{version={version} amount={permission_amount}}}",
            version = self.latest_variable_version,
            permission_amount = self.permission_amount
        )
    }
}

impl<const IS_DEAD: bool> std::fmt::Display for LifetimeTokens<IS_DEAD> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (lifetime, token) in &self.tokens {
            writeln!(f, "{}: {}", lifetime, token)?;
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
        let lifetime: LifetimeVariable = local.variable.name.clone().into();
        let permission_amount_is_non_negative = vir_low::Statement::assert(
            vir_low::Expression::greater_equals(
                (*predicate.permission).clone(),
                vir_low::Expression::no_permission(),
            ),
            position,
        );
        if let Some(token) = self.tokens.get_mut(&lifetime.name) {
            assert_eq!(
                token.latest_variable_version, lifetime.version,
                "lifetime: {}",
                lifetime.name
            );
            token.permission_amount = vir_low::Expression::perm_binary_op(
                vir_low::PermBinaryOpKind::Add,
                token.permission_amount.clone(),
                *predicate.permission,
                position,
            )
            .simplify_perm();
        } else {
            self.tokens.insert(
                lifetime.name.clone(),
                LifetimeToken {
                    latest_variable_version: lifetime.version,
                    permission_amount: *predicate.permission,
                },
            );
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
        let lifetime: LifetimeVariable = local.variable.name.clone().into();
        let mut token = self.tokens.remove(&lifetime.name).unwrap();
        assert_eq!(
            token.latest_variable_version, lifetime.version,
            "lifetime: {}",
            lifetime.name
        );
        token.permission_amount = vir_low::Expression::perm_binary_op(
            vir_low::PermBinaryOpKind::Sub,
            token.permission_amount,
            *predicate.permission,
            position,
        );
        token.permission_amount = token.permission_amount.simplify_perm();
        if !token.permission_amount.is_no_permission() {
            let permission_amount_is_non_negative = vir_low::Statement::assert(
                vir_low::Expression::greater_equals(
                    token.permission_amount.clone(),
                    vir_low::Expression::no_permission(),
                ),
                position,
            );
            block_builder.add_statement(permission_amount_is_non_negative)?;
            self.tokens.insert(lifetime.name.clone(), token);
        }
        // let latest_version = self
        //     .latest_variable_versions
        //     .get(&lifetime_with_version.name)
        //     .unwrap();
        // assert_eq!(
        //     latest_version, &lifetime_with_version.version,
        //     "lifetime: {}",
        //     lifetime_with_version.name
        // );
        // let mut lifetime = local.variable.name.clone();
        // if let Some(cannonical_lifetime) =
        //     constraints.resolve_cannonical_lifetime_name(&lifetime)?
        // {
        //     lifetime = cannonical_lifetime.to_string();
        // }
        // if let Some(mut amount) = self.token_permission_amounts.remove(&lifetime) {
        //     if IS_DEAD {
        //         // Since DeadLifetimeToken is duplicable, the exhale only
        //         // asserts that we have the permission.
        //     } else {
        //         amount = vir_low::Expression::perm_binary_op(
        //             vir_low::PermBinaryOpKind::Sub,
        //             amount,
        //             *predicate.permission,
        //             position,
        //         );
        //         amount = amount.simplify_perm();
        //     }
        //     if !amount.is_no_permission() {
        //         self.token_permission_amounts
        //             .insert(lifetime, amount.clone());
        //         let permission_amount_is_non_negative = vir_low::Statement::assert(
        //             vir_low::Expression::greater_equals(
        //                 amount,
        //                 vir_low::Expression::no_permission(),
        //             ),
        //             position,
        //         );
        //         block_builder.add_statement(permission_amount_is_non_negative)?;
        //     } else {
        //         self.latest_variable_versions
        //             .remove(&lifetime_with_version.name);
        //     }
        // } else if config::panic_on_failed_exhale() {
        //     panic!("failed to exhale: {predicate}\n{self}");
        // } else {
        //     // It could be that the permission tracking is not precise enough. Emit a conditional exhale.
        //     let mut sum = vir_low::Expression::no_permission();
        //     for (chunk_lifetime, amount) in &self.token_permission_amounts {
        //         sum = vir_low::Expression::perm_binary_op_no_pos(
        //             vir_low::PermBinaryOpKind::Add,
        //             sum,
        //             vir_low::Expression::conditional_no_pos(
        //                 vir_low::Expression::equals(
        //                     local.variable.clone().into(),
        //                     vir_low::VariableDecl::new(
        //                         chunk_lifetime.clone(),
        //                         local.variable.ty.clone(),
        //                     )
        //                     .into(),
        //                 ),
        //                 amount.clone(),
        //                 vir_low::Expression::no_permission(),
        //             ),
        //         );
        //     }
        //     block_builder.add_statement(vir_low::Statement::comment(format!(
        //         "Failed to syntactically exhale: {predicate} {lifetime} at {position}"
        //     )))?;
        //     block_builder.add_statement(
        //         vir_low::Statement::assert_no_pos(vir_low::Expression::greater_equals(
        //             sum,
        //             *predicate.permission,
        //         ))
        //         .set_default_position(position),
        //     )?;
        // }
        Ok(())
    }

    pub(super) fn merge(
        &mut self,
        other: &Self,
        self_edge_block: &mut Vec<vir_low::Statement>,
        other_edge_block: &mut Vec<vir_low::Statement>,
        position: vir_low::Position,
        constraints_merge_report: &ConstraintsMergeReport,
    ) -> SpannedEncodingResult<()> {
        for (lifetime, token) in &mut self.tokens {
            token.latest_variable_version = constraints_merge_report
                .resolve_self_latest_lifetime_variable_version(
                    lifetime,
                    token.latest_variable_version,
                );
            if let Some(other_token) = other.tokens.get(lifetime) {
                let latest_other_version = constraints_merge_report
                    .resolve_other_latest_lifetime_variable_version(
                        lifetime,
                        other_token.latest_variable_version,
                    );
                assert_eq!(
                    token.latest_variable_version, latest_other_version,
                    "lifetime: {}",
                    lifetime
                );
                assert_eq!(
                    token.permission_amount, other_token.permission_amount,
                    "lifetime: {}",
                    lifetime
                );
            } else {
                // Did not find the lifetime token in the other block, mark that
                // edge as unreachable. This can happen if the reference was not
                // closed on some (potentially unreachable) path.
                other_edge_block.push(
                    vir_low::Statement::comment(format!(
                        "marking as unreachable because not found in other: {lifetime}"
                    ))
                    .set_default_position(position),
                );
                other_edge_block.push(
                    vir_low::Statement::assert_no_pos(false.into()).set_default_position(position),
                );
            }
        }
        for (lifetime, token) in &other.tokens {
            if !self.tokens.contains_key(lifetime) {
                // Did not find the lifetime token in the self block, mark that
                // edge as unreachable. This can happen if the reference was not
                // closed on some (potentially unreachable) path.
                self_edge_block.push(
                    vir_low::Statement::comment(format!(
                        "marking as unreachable because not found in other: {lifetime}"
                    ))
                    .set_default_position(position),
                );
                self_edge_block.push(
                    vir_low::Statement::assert_no_pos(false.into()).set_default_position(position),
                );
                let latest_other_version = constraints_merge_report
                    .resolve_other_latest_lifetime_variable_version(
                        lifetime,
                        token.latest_variable_version,
                    );
                let token = LifetimeToken {
                    latest_variable_version: latest_other_version,
                    permission_amount: token.permission_amount.clone(),
                };
                self.tokens.insert(lifetime.clone(), token);
            }
        }
        // for (mut lifetime, amount) in std::mem::take(&mut self.token_permission_amounts) {
        //     let other_amount = if let Some(other_amount) =
        //         other.token_permission_amounts.get(&lifetime)
        //     {
        //         other_amount
        //     } else {
        //         if let Some(cannonical_self) =
        //             constraints_merge_report.resolve_new_self_cannonical_lifetime_name(&lifetime)
        //         {
        //             lifetime = cannonical_self.clone();
        //         }
        //         if let Some(other_lifetime) =
        //             constraints_merge_report.resolve_old_other_cannonical_lifetime_name(&lifetime)
        //         {
        //             if let Some(other_amount) = other.token_permission_amounts.get(other_lifetime) {
        //                 other_amount
        //             } else {
        //                 // Did not find the lifetime in the other block, mark that
        //                 // edge as unreachable. This can happen if the reference was
        //                 // not closed on some (potentially unreachable) trace.
        //                 other_edge_block.push(
        //                     vir_low::Statement::comment(format!(
        //                         "marking as unreachable because not found in other: {lifetime}"
        //                     ))
        //                     .set_default_position(position),
        //                 );
        //                 other_edge_block.push(
        //                     vir_low::Statement::assert_no_pos(false.into())
        //                         .set_default_position(position),
        //                 );
        //                 self.token_permission_amounts
        //                     .insert(lifetime.clone(), amount.clone());
        //                 continue;
        //             }
        //         } else {
        //             // Did not find the lifetime in the other block, mark that
        //             // edge as unreachable. This can happen if the reference was
        //             // not closed on some (potentially unreachable) trace.
        //             other_edge_block.push(
        //                 vir_low::Statement::comment(format!(
        //                     "marking as unreachable because not found in other: {lifetime}"
        //                 ))
        //                 .set_default_position(position),
        //             );
        //             other_edge_block.push(
        //                 vir_low::Statement::assert_no_pos(false.into())
        //                     .set_default_position(position),
        //             );
        //             self.token_permission_amounts
        //                 .insert(lifetime.clone(), amount.clone());
        //             continue;
        //         }
        //     };
        //     assert_eq!(
        //         &amount, other_amount,
        //         "{lifetime}: {amount} != {other_amount}"
        //     );
        //     self.token_permission_amounts.insert(lifetime, amount);
        // }
        // for (lifetime, amount) in &other.token_permission_amounts {
        //     let self_amount = if let Some(self_amount) = self.token_permission_amounts.get(lifetime)
        //     {
        //         self_amount
        //     } else {
        //         if let Some(self_lifetime) =
        //             constraints_merge_report.resolve_new_other_cannonical_lifetime_name(lifetime)
        //         {
        //             if let Some(self_amount) = self.token_permission_amounts.get(self_lifetime) {
        //                 self_amount
        //             } else {
        //                 // Did not find the lifetime in the other block, mark that
        //                 // edge as unreachable. This can happen if the reference was
        //                 // not closed on some (potentially unreachable) trace.
        //                 self_edge_block.push(
        //                     vir_low::Statement::comment(format!(
        //                         "marking as unreachable because not found in self: {lifetime}"
        //                     ))
        //                     .set_default_position(position),
        //                 );
        //                 self_edge_block.push(
        //                     vir_low::Statement::assert_no_pos(false.into())
        //                         .set_default_position(position),
        //                 );
        //                 self.token_permission_amounts
        //                     .insert(lifetime.clone(), amount.clone());
        //                 continue;
        //             }
        //         } else {
        //             // Did not find the lifetime in the other block, mark that
        //             // edge as unreachable. This can happen if the reference was
        //             // not closed on some (potentially unreachable) trace.
        //             self_edge_block.push(
        //                 vir_low::Statement::comment(format!(
        //                     "marking as unreachable because not found in self: {lifetime}"
        //                 ))
        //                 .set_default_position(position),
        //             );
        //             self_edge_block.push(
        //                 vir_low::Statement::assert_no_pos(false.into())
        //                     .set_default_position(position),
        //             );
        //             self.token_permission_amounts
        //                 .insert(lifetime.clone(), amount.clone());
        //             continue;
        //         }
        //     };
        //     assert_eq!(self_amount, amount);
        // }

        // TODO: Problem: Lifetime tokens can be aliased and in that case I need to sum their permissions, which I do not do. As a result,
        // when some lifetime token is exhaled, it may also exhale aliased lifetime tokens.

        eprintln!("after merge:\n{self}");
        Ok(())
    }

    pub(super) fn leak_check(&self) -> SpannedEncodingResult<()> {
        for (lifetime, token) in &self.tokens {
            error!(
                "ERROR: Lifetime token {} was not exhaled. Its amount is {}.",
                lifetime, token
            );
        }
        assert!(self.tokens.is_empty());
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
