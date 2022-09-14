use super::{GlobalHeapState, HeapMergeReport};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::symbolic_execution_new::{
        block_builder::BlockBuilder, procedure_executor::constraints::BlockConstraints,
    },
};
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low},
};

#[derive(Default, Clone)]
pub(super) struct DeadLifetimeTokens {
    /// A set of lifetimes for which we for sure have dead lifetime tokens.
    dead_lifetime_tokens: BTreeSet<String>,
    /// A map from lifetimes to which we potentially have a dead lifetime token
    /// to variables used to track the actual permission amount.
    potentially_dead_lifetime_token_permissions: BTreeMap<String, vir_low::VariableDecl>,
}

impl std::fmt::Display for DeadLifetimeTokens {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "dead lifetime tokens:")?;
        for lifetime in &self.dead_lifetime_tokens {
            writeln!(f, "  {lifetime}")?;
        }
        writeln!(f, "potentially dead lifetime tokens:")?;
        for (lifetime, permission) in &self.potentially_dead_lifetime_token_permissions {
            writeln!(f, "  {lifetime}: {permission}")?;
        }
        Ok(())
    }
}

impl DeadLifetimeTokens {
    pub(super) fn inhale(
        &mut self,
        global_state: &mut GlobalHeapState,
        mut predicate: vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        assert_eq!(predicate.arguments.len(), 1);
        let Some(vir_low::Expression::Local(local)) = predicate.arguments.pop() else {
            unimplemented!("TODO: A proper error message.");
        };
        let lifetime = local.variable.name;
        self.dead_lifetime_tokens.insert(lifetime);
        Ok(())
    }

    pub(super) fn exhale(
        &mut self,
        mut predicate: vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
        constraints: &mut BlockConstraints,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        assert_eq!(predicate.arguments.len(), 1);
        let Some(vir_low::Expression::Local(local)) = predicate.arguments.pop() else {
            unimplemented!("TODO: A proper error message.");
        };
        let lifetime = local.variable.name;
        // Since DeadLifetimeToken is duplicable, we only need to assert that we
        // have the permission.
        if self.dead_lifetime_tokens.contains(&lifetime) {
            // We certainly have the permission, nothing to do.
            return Ok(());
        }
        let cannonical_lifetime = constraints.resolve_cannonical_lifetime_name(&lifetime)?;
        if let Some(cannonical_lifetime) = &cannonical_lifetime {
            if self.dead_lifetime_tokens.contains(*cannonical_lifetime) {
                // We certainly have the permission, nothing to do.
                return Ok(());
            }
        }
        if let Some(permission) = self
            .potentially_dead_lifetime_token_permissions
            .get(&lifetime)
        {
            // We potentially have the permission, but the verifier needs to check.
            block_builder.add_statement(
                vir_low::Statement::assign_no_pos(
                    permission.clone(),
                    vir_low::Expression::full_permission(),
                )
                .set_default_position(position),
            )?;
            return Ok(());
        }
        if let Some(cannonical_lifetime) = &cannonical_lifetime {
            if let Some(permission) = self
                .potentially_dead_lifetime_token_permissions
                .get(*cannonical_lifetime)
            {
                // We potentially have the permission, but the verifier needs to check.
                block_builder.add_statement(
                    vir_low::Statement::assign_no_pos(
                        permission.clone(),
                        vir_low::Expression::full_permission(),
                    )
                    .set_default_position(position),
                )?;
                return Ok(());
            }
        }
        for eq in constraints.get_equal_lifetimes(&lifetime)? {
            eprintln!("  {eq} == {lifetime}");
        }
        unimplemented!("TODO: this should be unreachable: {lifetime}\n{self}");
    }

    /// This function spreads the permission over known e-classes of lifetimes
    /// for which we have permission
    pub(super) fn spread_permission_over_eclasses(
        &mut self,
        constraints: &mut BlockConstraints,
    ) -> SpannedEncodingResult<()> {
        for lifetime in std::mem::take(&mut self.dead_lifetime_tokens) {
            self.dead_lifetime_tokens
                .extend(constraints.get_equal_lifetimes(&lifetime)?);
            self.dead_lifetime_tokens.insert(lifetime);
        }
        for (lifetime, permission) in
            std::mem::take(&mut self.potentially_dead_lifetime_token_permissions)
        {
            for equal_lifetime in constraints.get_equal_lifetimes(&lifetime)? {
                if !self
                    .potentially_dead_lifetime_token_permissions
                    .contains_key(&equal_lifetime)
                {
                    self.potentially_dead_lifetime_token_permissions
                        .insert(equal_lifetime, permission.clone());
                }
            }
            self.potentially_dead_lifetime_token_permissions
                .insert(lifetime, permission);
        }
        Ok(())
    }

    pub(super) fn merge(
        &mut self,
        other: &Self,
        heap_merge_report: &mut HeapMergeReport,
        global_state: &mut GlobalHeapState,
    ) -> SpannedEncodingResult<()> {
        let predicate_name = "DeadLifetimeToken";
        // First, intersect the guaranteed sets and obtain the new potential
        // sets.
        let new_self_potentially_dead_lifetimes: Vec<_> = self
            .dead_lifetime_tokens
            .drain_filter(|lifetime| other.dead_lifetime_tokens.contains(lifetime))
            .collect();
        let new_other_potentially_dead_lifetimes = other
            .dead_lifetime_tokens
            .iter()
            .filter(|lifetime| !self.dead_lifetime_tokens.contains(*lifetime));
        // Generate fresh permission variables for all potentially dead
        // lifetimes.
        for (lifetime, old_self_permission) in &mut self.potentially_dead_lifetime_token_permissions
        {
            if let Some(old_other_permission) = other
                .potentially_dead_lifetime_token_permissions
                .get(lifetime)
            {
                let new_permission_variable = heap_merge_report.remap_permission_variable(
                    predicate_name,
                    old_self_permission,
                    old_other_permission,
                    global_state,
                );
                *old_self_permission = new_permission_variable;
            }
        }
        for (lifetime, old_other_permission) in &other.potentially_dead_lifetime_token_permissions {
            if !self
                .potentially_dead_lifetime_token_permissions
                .contains_key(lifetime)
            {
                self.potentially_dead_lifetime_token_permissions
                    .insert(lifetime.clone(), old_other_permission.clone());
            }
        }
        for lifetime in new_self_potentially_dead_lifetimes {
            if let Some(permission_variable) = self
                .potentially_dead_lifetime_token_permissions
                .get(&lifetime)
            {
                heap_merge_report.set_write_in_all_predecessors_except_last(permission_variable);
            } else {
                let permission_variable = global_state.create_permission_variable(predicate_name);
                heap_merge_report.set_write_in_all_predecessors_except_last(&permission_variable);
                self.potentially_dead_lifetime_token_permissions
                    .insert(lifetime, permission_variable);
            }
        }
        for lifetime in new_other_potentially_dead_lifetimes {
            if let Some(permission_variable) = self
                .potentially_dead_lifetime_token_permissions
                .get(lifetime)
            {
                heap_merge_report.set_write_in_last_predecessor(permission_variable.clone());
            } else {
                let permission_variable = global_state.create_permission_variable(predicate_name);
                heap_merge_report.set_write_in_last_predecessor(permission_variable.clone());
                self.potentially_dead_lifetime_token_permissions
                    .insert(lifetime.clone(), permission_variable);
            }
        }
        Ok(())
    }
}
