use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    mir::{
        errors::ErrorInterface,
        procedures::encoder::{scc::*, ProcedureEncoder},
    },
};
use prusti_interface::environment::{
    debug_utils::to_text::ToText, mir_body::borrowck::facts::RichLocation,
};
use prusti_rustc_interface::middle::mir;
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::high::{self as vir_high, builders::procedure::BasicBlockBuilder};

pub(super) trait LifetimesEncoder<'tcx> {
    fn encode_lft_for_statement_start(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        original_lifetimes: &mut BTreeSet<String>,
        derived_lifetimes: &mut BTreeMap<String, BTreeSet<String>>,
        statement: Option<&mir::Statement<'tcx>>,
    ) -> SpannedEncodingResult<()>;
    fn encode_lft_for_statement_mid(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        original_lifetimes: &mut BTreeSet<String>,
        derived_lifetimes: &mut BTreeMap<String, BTreeSet<String>>,
        statement: Option<&mir::Statement<'tcx>>,
    ) -> SpannedEncodingResult<()>;
    fn reborrow_lifetimes(
        &mut self,
        statement: Option<&mir::Statement<'tcx>>,
    ) -> SpannedEncodingResult<Option<(String, BTreeSet<String>)>>;
    fn reborrow_operand_lifetime(
        &mut self,
        statement: Option<&mir::Statement<'tcx>>,
    ) -> Option<String>;
    fn encode_lft_for_block(
        &mut self,
        target: mir::BasicBlock,
        location: mir::Location,
        block_builder: &mut BasicBlockBuilder,
    ) -> SpannedEncodingResult<()>;
    fn encode_lft_for_block_with_edge(
        &mut self,
        target: mir::BasicBlock,
        encoded_target: vir_high::BasicBlockId,
        location: mir::Location,
        block_builder: &mut BasicBlockBuilder,
    ) -> SpannedEncodingResult<vir_high::BasicBlockId>;
    #[allow(clippy::too_many_arguments)]
    fn encode_lft(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        old_original_lifetimes: &mut BTreeSet<String>,
        old_derived_lifetimes: &mut BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &mut BTreeMap<String, BTreeSet<String>>,
        shorten_lifetime_takes: bool,
        new_reborrow_lifetime_to_remove: Option<String>,
        reborrow_lifetimes: Option<(String, BTreeSet<String>)>,
    ) -> SpannedEncodingResult<()>;
    fn update_lifetimes_to_remove(
        &mut self,
        old_original_lifetimes: &BTreeSet<String>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        new_reborrow_lifetime_to_remove: String,
        lifetimes_to_create: &BTreeSet<String>,
    );
    fn remove_reborrow_lifetimes_set(&mut self, set: &mut BTreeSet<String>);
    fn remove_reborrow_lifetimes_map(&mut self, map: &mut BTreeMap<String, BTreeSet<String>>);
    fn lifetime_backups(
        &mut self,
        old_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        lifetime_backups: &mut BTreeMap<String, (String, vir_high::Local)>,
    ) -> SpannedEncodingResult<()>;
    fn encode_obtain_mut_ref(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        lifetime_backups: &BTreeMap<String, (String, vir_high::Local)>,
    ) -> SpannedEncodingResult<()>;
    fn encode_lifetime_backups(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        lifetime_backups: &BTreeMap<String, (String, vir_high::Local)>,
    ) -> SpannedEncodingResult<()>;
    fn encode_bor_shorten(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        lifetime_backups: &BTreeMap<String, (String, vir_high::Local)>,
    ) -> SpannedEncodingResult<()>;
    fn encode_new_lft(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        lifetimes_to_create: &BTreeSet<String>,
    ) -> SpannedEncodingResult<()>;
    fn encode_end_lft(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        old_original_lifetimes: &BTreeSet<String>,
        new_original_lifetimes: &BTreeSet<String>,
    ) -> SpannedEncodingResult<()>;
    fn encode_lft_return(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        old_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
    ) -> SpannedEncodingResult<()>;
    fn encode_lft_take(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        old_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        reborrow_lifetimes: &Option<(String, BTreeSet<String>)>,
    ) -> SpannedEncodingResult<()>;
    fn encode_dead_inclusion(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        new_original_lifetimes: &BTreeSet<String>,
    ) -> SpannedEncodingResult<()>;
    fn encode_dead_lifetime(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        lifetime: vir_high::ty::LifetimeConst,
    ) -> SpannedEncodingResult<()>;
    fn encode_lifetimes_dead_on_edge(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        from: RichLocation,
        to: RichLocation,
    ) -> SpannedEncodingResult<()>;
    fn encode_lft_assert_subset(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        lifetime_lhs: String,
        lifetime_rhs: String,
    ) -> SpannedEncodingResult<()>;
    fn encode_lft_variable(
        &self,
        variable_name: String,
    ) -> SpannedEncodingResult<vir_high::VariableDecl>;
    fn lifetimes_to_return(
        &mut self,
        old_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
    ) -> BTreeMap<String, BTreeSet<String>>;
    fn lifetimes_to_take(
        &mut self,
        old_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
    ) -> BTreeMap<String, BTreeSet<String>>;
    fn lifetimes_to_end(
        &mut self,
        old_original_lifetimes: &BTreeSet<String>,
        new_original_lifetimes: &BTreeSet<String>,
    ) -> BTreeSet<String>;
    fn lifetimes_to_create(
        &mut self,
        old_original_lifetimes: &BTreeSet<String>,
        new_original_lifetimes: &BTreeSet<String>,
    ) -> BTreeSet<String>;
    fn lifetime_token_fractional_permission(&self, denominator: usize) -> vir_high::Expression;
    fn encode_lifetime_specifications(
        &mut self,
    ) -> SpannedEncodingResult<(Vec<vir_high::Statement>, Vec<vir_high::Statement>)>;
    fn identical_lifetimes_map(
        &mut self,
        existing_lifetimes: BTreeSet<String>,
        relations: BTreeSet<(String, String)>,
    ) -> BTreeMap<String, String>;
    fn opaque_lifetimes(&mut self) -> SpannedEncodingResult<Vec<vir_high::ty::LifetimeConst>>;
    fn encode_inhale_lifetime_token(
        &mut self,
        lifetime_const: vir_high::ty::LifetimeConst,
        permission_amount: vir_high::Expression,
    ) -> SpannedEncodingResult<vir_high::Statement>;
    fn encode_inhale_lifetime_tokens(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        lifetime_names: &[String],
        permission_divisor_mult: usize,
    ) -> SpannedEncodingResult<()>;
    fn encode_exhale_lifetime_token(
        &mut self,
        lifetime_const: vir_high::ty::LifetimeConst,
        permission_amount: vir_high::Expression,
    ) -> SpannedEncodingResult<vir_high::Statement>;
    fn encode_exhale_lifetime_tokens(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        lifetime_names: &[String],
        permission_divisor_mult: usize,
    ) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> LifetimesEncoder<'tcx> for ProcedureEncoder<'p, 'v, 'tcx> {
    fn encode_lft_for_statement_start(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        original_lifetimes: &mut BTreeSet<String>,
        derived_lifetimes: &mut BTreeMap<String, BTreeSet<String>>,
        statement: Option<&mir::Statement<'tcx>>,
    ) -> SpannedEncodingResult<()> {
        let mut new_derived_lifetimes = self.lifetimes.get_origin_contains_loan_at_start(location);
        block_builder.add_comment(format!(
            "Prepare lifetimes for statement start {location:?}"
        ));
        let new_reborrow_lifetime_to_ignore: Option<String> =
            self.reborrow_operand_lifetime(statement);
        self.encode_lft(
            block_builder,
            location,
            original_lifetimes,
            derived_lifetimes,
            &mut new_derived_lifetimes,
            false,
            new_reborrow_lifetime_to_ignore,
            None,
        )?;
        Ok(())
    }

    fn encode_lft_for_statement_mid(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        original_lifetimes: &mut BTreeSet<String>,
        derived_lifetimes: &mut BTreeMap<String, BTreeSet<String>>,
        statement: Option<&mir::Statement<'tcx>>,
    ) -> SpannedEncodingResult<()> {
        let mut new_derived_lifetimes = self.lifetimes.get_origin_contains_loan_at_mid(location);
        block_builder.add_comment(format!("Prepare lifetimes for statement mid {location:?}"));
        let new_reborrow_lifetime_to_ignore: Option<String> =
            self.reborrow_operand_lifetime(statement);
        // FIXME: The lifetimes read via the reborrow statement are currently not killed.
        let reborrow_lifetimes = self.reborrow_lifetimes(statement)?;
        self.encode_lft(
            block_builder,
            location,
            original_lifetimes,
            derived_lifetimes,
            &mut new_derived_lifetimes,
            false,
            new_reborrow_lifetime_to_ignore,
            reborrow_lifetimes,
        )?;
        Ok(())
    }

    fn reborrow_lifetimes(
        &mut self,
        statement: Option<&mir::Statement<'tcx>>,
    ) -> SpannedEncodingResult<Option<(String, BTreeSet<String>)>> {
        if let Some(statement) = statement {
            if let mir::StatementKind::Assign(box (
                target,
                mir::Rvalue::Ref(region, _borrow_kind, place),
            )) = &statement.kind
            {
                let target_lifetime = self.procedure.get_lifetime_of_var(target.local);
                let operand_lifetime: String = region.to_text();
                if let Some((reference, _projection)) = place.iter_projections().last() {
                    let value_lifetime = self.procedure.get_lifetime_of_var(reference.local);
                    if let (Some(target_lifetime), Some(value_lifetime)) =
                        (target_lifetime, value_lifetime)
                    {
                        let values = [operand_lifetime, target_lifetime]
                            .iter()
                            .cloned()
                            .collect();
                        return Ok(Some((value_lifetime, values)));
                    }
                }
            }
        }
        Ok(None)
    }

    fn reborrow_operand_lifetime(
        &mut self,
        statement: Option<&mir::Statement<'tcx>>,
    ) -> Option<String> {
        if let Some(statement) = statement {
            if let mir::StatementKind::Assign(box (
                _target,
                mir::Rvalue::Ref(region, _borrow_kind, place),
            )) = &statement.kind
            {
                let region_name: String = region.to_text();
                if let Some((_ref, projection)) = place.iter_projections().last() {
                    if projection == mir::ProjectionElem::Deref {
                        return Some(region_name);
                    }
                }
            }
        }
        None
    }

    fn encode_lft_for_block(
        &mut self,
        target: mir::BasicBlock,
        location: mir::Location,
        block_builder: &mut BasicBlockBuilder,
    ) -> SpannedEncodingResult<()> {
        let mut needed_derived_lifetimes = self.needed_derived_lifetimes_for_block(&target);
        let mut current_derived_lifetimes =
            self.lifetimes.get_origin_contains_loan_at_mid(location);
        let mut current_original_lifetimes = self.lifetimes.get_loan_live_at_start(location);
        block_builder.add_comment(format!("Prepare lifetimes for block {target:?}"));
        self.encode_lft(
            block_builder,
            location,
            &mut current_original_lifetimes,
            &mut current_derived_lifetimes,
            &mut needed_derived_lifetimes,
            true,
            None,
            None,
        )?;
        self.reborrow_lifetimes_to_remove_for_block
            .entry(target)
            .or_default();
        let mut values = self
            .reborrow_lifetimes_to_remove_for_block
            .get(&self.current_basic_block.unwrap())
            .unwrap()
            .clone();
        self.reborrow_lifetimes_to_remove_for_block
            .get_mut(&target)
            .unwrap()
            .append(&mut values);
        Ok(())
    }

    fn encode_lft_for_block_with_edge(
        &mut self,
        target: mir::BasicBlock,
        encoded_target: vir_high::BasicBlockId,
        location: mir::Location,
        block_builder: &mut BasicBlockBuilder,
    ) -> SpannedEncodingResult<vir_high::BasicBlockId> {
        let mut needed_derived_lifetimes = self.needed_derived_lifetimes_for_block(&target);
        let mut current_derived_lifetimes =
            self.lifetimes.get_origin_contains_loan_at_mid(location);
        let mut current_original_lifetimes = self.lifetimes.get_loan_live_at_start(location);
        let fresh_destination_label = self.fresh_basic_block_label();
        let mut intermediate_block_builder =
            block_builder.create_basic_block_builder(fresh_destination_label.clone());
        intermediate_block_builder.add_comment(format!("Prepare lifetimes for block {target:?}"));
        self.encode_lft(
            &mut intermediate_block_builder,
            location,
            &mut current_original_lifetimes,
            &mut current_derived_lifetimes,
            &mut needed_derived_lifetimes,
            true,
            None,
            None,
        )?;
        self.reborrow_lifetimes_to_remove_for_block
            .entry(target)
            .or_default();
        let mut values = self
            .reborrow_lifetimes_to_remove_for_block
            .get(&self.current_basic_block.unwrap())
            .unwrap()
            .clone();
        self.reborrow_lifetimes_to_remove_for_block
            .get_mut(&target)
            .unwrap()
            .append(&mut values);
        intermediate_block_builder.set_successor_jump(vir_high::Successor::Goto(encoded_target));
        intermediate_block_builder.build();
        Ok(fresh_destination_label)
    }

    /// Adds all statements needed for the encoding of the location.
    fn encode_lft(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        old_original_lifetimes: &mut BTreeSet<String>,
        old_derived_lifetimes: &mut BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &mut BTreeMap<String, BTreeSet<String>>,
        shorten_lifetimes: bool,
        new_reborrow_lifetime_to_remove: Option<String>,
        reborrow_lifetimes: Option<(String, BTreeSet<String>)>,
    ) -> SpannedEncodingResult<()> {
        let mut new_original_lifetimes: BTreeSet<String> = new_derived_lifetimes
            .clone()
            .into_values()
            .flatten()
            .collect();
        let mut lifetimes_to_create =
            self.lifetimes_to_create(old_original_lifetimes, &new_original_lifetimes);
        let mut lifetime_backups: BTreeMap<String, (String, vir_high::Local)> = BTreeMap::new();
        if let Some(new_reborrow_lifetime_to_remove) = new_reborrow_lifetime_to_remove {
            self.update_lifetimes_to_remove(
                old_original_lifetimes,
                new_derived_lifetimes,
                new_reborrow_lifetime_to_remove,
                &lifetimes_to_create,
            );
        }
        self.remove_reborrow_lifetimes_set(&mut lifetimes_to_create);
        self.remove_reborrow_lifetimes_set(&mut new_original_lifetimes);
        self.remove_reborrow_lifetimes_set(old_original_lifetimes);
        self.remove_reborrow_lifetimes_map(old_derived_lifetimes);
        self.remove_reborrow_lifetimes_map(new_derived_lifetimes);
        if shorten_lifetimes {
            self.lifetime_backups(
                old_derived_lifetimes,
                new_derived_lifetimes,
                &mut lifetime_backups,
            )?;
            self.encode_lifetime_backups(block_builder, location, &lifetime_backups)?;
        }
        self.encode_lft_return(
            block_builder,
            location,
            old_derived_lifetimes,
            new_derived_lifetimes,
        )?;
        self.encode_end_lft(
            block_builder,
            location,
            old_original_lifetimes,
            &new_original_lifetimes,
        )?;
        self.encode_dead_inclusion(block_builder, location, &new_original_lifetimes)?;
        self.encode_new_lft(block_builder, location, &lifetimes_to_create)?;
        if shorten_lifetimes {
            self.encode_obtain_mut_ref(block_builder, location, &lifetime_backups)?;
        }
        self.encode_lft_take(
            block_builder,
            location,
            old_derived_lifetimes,
            new_derived_lifetimes,
            &reborrow_lifetimes,
        )?;
        self.encode_bor_shorten(block_builder, location, &lifetime_backups)?;

        *old_original_lifetimes = new_original_lifetimes.clone();
        *old_derived_lifetimes = new_derived_lifetimes.clone();
        Ok(())
    }

    fn update_lifetimes_to_remove(
        &mut self,
        old_original_lifetimes: &BTreeSet<String>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        lifetime_to_ignore: String,
        lifetimes_to_create: &BTreeSet<String>,
    ) {
        let mut new_lifetimes_to_ignore: BTreeSet<String> = BTreeSet::new();
        for (lifetime, derived_from) in new_derived_lifetimes.clone() {
            // NOTE: if the lifetime is not derived from at least one already existing
            //   original lifetime, we can not delete the lifetimes it is derived from.
            let can_remove_lifetimes = !derived_from
                .iter()
                .filter(|&x| old_original_lifetimes.contains(x))
                .cloned()
                .collect::<BTreeSet<String>>()
                .is_empty();
            if lifetime == lifetime_to_ignore && can_remove_lifetimes {
                new_lifetimes_to_ignore = derived_from
                    .clone()
                    .iter()
                    .filter(|x| lifetimes_to_create.contains(*x))
                    .cloned()
                    .collect();
            }
        }
        self.reborrow_lifetimes_to_remove_for_block
            .get_mut(&self.current_basic_block.unwrap())
            .unwrap()
            .append(&mut new_lifetimes_to_ignore);
    }

    fn remove_reborrow_lifetimes_set(&mut self, set: &mut BTreeSet<String>) {
        *set = set
            .clone()
            .iter()
            .filter(|&lft| {
                !self
                    .reborrow_lifetimes_to_remove_for_block
                    .get(&self.current_basic_block.unwrap())
                    .unwrap()
                    .contains(lft)
            })
            .cloned()
            .collect();
    }

    fn remove_reborrow_lifetimes_map(&mut self, map: &mut BTreeMap<String, BTreeSet<String>>) {
        *map = map
            .clone()
            .iter()
            .map(|(lifetime, derived_from)| {
                let updated_derived_from: BTreeSet<String> = derived_from
                    .clone()
                    .iter()
                    .filter(|&lft| {
                        !self
                            .reborrow_lifetimes_to_remove_for_block
                            .get(&self.current_basic_block.unwrap())
                            .unwrap()
                            .contains(lft)
                    })
                    .cloned()
                    .collect();
                (lifetime.clone(), updated_derived_from)
            })
            .collect();
    }

    fn encode_bor_shorten(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        lifetime_backups: &BTreeMap<String, (String, vir_high::Local)>,
    ) -> SpannedEncodingResult<()> {
        for (lifetime, (old_lifetime, object)) in lifetime_backups {
            block_builder.add_statement(self.set_statement_error(
                location,
                ErrorCtxt::LifetimeEncoding,
                vir_high::Statement::bor_shorten_no_pos(
                    vir_high::ty::LifetimeConst {
                        name: lifetime.to_string(),
                    },
                    vir_high::ty::LifetimeConst {
                        name: old_lifetime.to_string(),
                    },
                    object.clone().into(),
                    self.lifetime_token_fractional_permission(self.lifetime_count),
                ),
            )?);
        }
        Ok(())
    }

    fn lifetime_backups(
        &mut self,
        old_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        lifetime_backups: &mut BTreeMap<String, (String, vir_high::Local)>,
    ) -> SpannedEncodingResult<()> {
        for (lifetime, _) in old_derived_lifetimes.clone() {
            if new_derived_lifetimes.contains_key(&lifetime) {
                if let Some(var) = self.procedure.get_var_of_lifetime(&lifetime[..]) {
                    let object = self.encode_local(var)?;
                    let backup_var_name =
                        format!("old_{}_{}", lifetime.clone(), self.old_lifetime_ctr);
                    self.old_lifetime_ctr += 1;
                    lifetime_backups.insert(lifetime.clone(), (backup_var_name.clone(), object));
                }
            }
        }
        Ok(())
    }

    fn encode_obtain_mut_ref(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        lifetime_backups: &BTreeMap<String, (String, vir_high::Local)>,
    ) -> SpannedEncodingResult<()> {
        for (lifetime, (_backup_var_name, object)) in lifetime_backups {
            block_builder.add_statement(self.set_statement_error(
                location,
                ErrorCtxt::LifetimeEncoding,
                vir_high::Statement::obtain_mut_ref_no_pos(
                    object.variable.clone().into(),
                    vir_high::ty::LifetimeConst {
                        name: lifetime.to_string(),
                    },
                ),
            )?);
        }
        Ok(())
    }

    fn encode_lifetime_backups(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        lifetime_backups: &BTreeMap<String, (String, vir_high::Local)>,
    ) -> SpannedEncodingResult<()> {
        for (lifetime, (backup_var_name, _object)) in lifetime_backups {
            let lifetime_var = vir_high::VariableDecl::new(lifetime, vir_high::ty::Type::Lifetime);
            let backup_var =
                vir_high::VariableDecl::new(backup_var_name, vir_high::ty::Type::Lifetime);
            block_builder.add_statement(self.set_statement_error(
                location,
                ErrorCtxt::LifetimeEncoding,
                vir_high::Statement::lifetime_take_no_pos(
                    backup_var,
                    vec![lifetime_var],
                    self.lifetime_token_fractional_permission(self.lifetime_count),
                ),
            )?);
        }
        Ok(())
    }

    fn encode_new_lft(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        lifetimes_to_create: &BTreeSet<String>,
    ) -> SpannedEncodingResult<()> {
        for lifetime in lifetimes_to_create {
            let lifetime_var = vir_high::VariableDecl::new(lifetime, vir_high::ty::Type::Lifetime);
            block_builder.add_statement(self.set_statement_error(
                location,
                ErrorCtxt::LifetimeEncoding,
                vir_high::Statement::new_lft_no_pos(lifetime_var),
            )?);
        }
        Ok(())
    }

    fn encode_end_lft(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        old_original_lifetimes: &BTreeSet<String>,
        new_original_lifetimes: &BTreeSet<String>,
    ) -> SpannedEncodingResult<()> {
        let lifetimes_to_end: BTreeSet<String> =
            self.lifetimes_to_end(old_original_lifetimes, new_original_lifetimes);
        for lifetime in lifetimes_to_end {
            let lifetime_var = vir_high::VariableDecl::new(lifetime, vir_high::ty::Type::Lifetime);
            block_builder.add_statement(self.set_statement_error(
                location,
                ErrorCtxt::LifetimeEncoding,
                vir_high::Statement::end_lft_no_pos(lifetime_var),
            )?);
        }
        Ok(())
    }

    fn encode_lft_return(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        old_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
    ) -> SpannedEncodingResult<()> {
        let lifetimes_to_return =
            self.lifetimes_to_return(old_derived_lifetimes, new_derived_lifetimes);
        for (lifetime, derived_from) in lifetimes_to_return {
            let encoded_target = self.encode_lft_variable(lifetime.clone())?;
            let mut lifetimes: Vec<vir_high::VariableDecl> = Vec::new();
            for lifetime_name in &derived_from {
                lifetimes.push(self.encode_lft_variable(lifetime_name.to_string())?);
            }
            self.derived_lifetimes_yet_to_kill
                .insert(lifetime.clone(), derived_from.clone());
            block_builder.add_statement(self.set_statement_error(
                location,
                ErrorCtxt::LifetimeEncoding,
                vir_high::Statement::lifetime_return_no_pos(
                    encoded_target,
                    lifetimes,
                    self.lifetime_token_fractional_permission(self.lifetime_count),
                ),
            )?);
        }
        Ok(())
    }

    fn encode_lft_take(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        old_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        reborrow_lifetimes: &Option<(String, BTreeSet<String>)>,
    ) -> SpannedEncodingResult<()> {
        let lifetimes_to_take =
            self.lifetimes_to_take(old_derived_lifetimes, new_derived_lifetimes);
        for (lifetime, derived_from) in lifetimes_to_take {
            let encoded_target = self.encode_lft_variable(lifetime.clone())?;
            let mut lifetimes: Vec<vir_high::VariableDecl> = Vec::new();
            assert!(!derived_from.is_empty());
            for lifetime_name in derived_from {
                lifetimes.push(self.encode_lft_variable(lifetime_name)?);
            }
            self.derived_lifetimes_yet_to_kill.remove(&lifetime[..]);
            block_builder.add_statement(self.set_statement_error(
                location,
                ErrorCtxt::LifetimeEncoding,
                vir_high::Statement::lifetime_take_no_pos(
                    encoded_target,
                    lifetimes,
                    self.lifetime_token_fractional_permission(self.lifetime_count),
                ),
            )?);
        }
        if let Some((value_lifetime, lifetimes)) = reborrow_lifetimes {
            let existing_lifetime = [self.encode_lft_variable(value_lifetime.clone())?].to_vec();
            for lifetime in lifetimes {
                if !new_derived_lifetimes.contains_key(lifetime) {
                    let encoded_target = self.encode_lft_variable(lifetime.clone())?;
                    block_builder.add_statement(self.set_statement_error(
                        location,
                        ErrorCtxt::LifetimeEncoding,
                        vir_high::Statement::lifetime_take_no_pos(
                            encoded_target,
                            existing_lifetime.clone(),
                            self.lifetime_token_fractional_permission(self.lifetime_count),
                        ),
                    )?);
                }
            }
        }
        Ok(())
    }

    fn encode_dead_inclusion(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        new_original_lifetimes: &BTreeSet<String>,
    ) -> SpannedEncodingResult<()> {
        for (lifetime, derived_from_lifetimes) in self.derived_lifetimes_yet_to_kill.clone() {
            for derived_from in derived_from_lifetimes.iter() {
                if !new_original_lifetimes.contains(derived_from) {
                    let encoded_target = self.encode_lft_variable(lifetime.clone())?;
                    let encoded_value = self.encode_lft_variable(derived_from.clone())?;
                    block_builder.add_statement(self.set_statement_error(
                        location,
                        ErrorCtxt::LifetimeEncoding,
                        vir_high::Statement::dead_inclusion_no_pos(encoded_target, encoded_value),
                    )?);
                    self.derived_lifetimes_yet_to_kill.remove(&lifetime);
                    break;
                }
            }
        }
        Ok(())
    }

    fn encode_dead_lifetime(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        lifetime: vir_high::ty::LifetimeConst,
    ) -> SpannedEncodingResult<()> {
        block_builder.add_statement(self.set_statement_error(
            location,
            ErrorCtxt::LifetimeEncoding,
            vir_high::Statement::dead_lifetime_no_pos(lifetime),
        )?);
        Ok(())
    }

    fn encode_lifetimes_dead_on_edge(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        from: RichLocation,
        to: RichLocation,
    ) -> SpannedEncodingResult<()> {
        for lifetime in self.lifetimes.get_lifetimes_dead_on_edge(from, to) {
            self.encode_dead_lifetime(
                block_builder,
                from.into_inner(),
                vir_high::ty::LifetimeConst::new(lifetime.to_text()),
            )?;
        }
        Ok(())
    }

    fn encode_lft_assert_subset(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        lifetime_lhs: String,
        lifetime_rhs: String,
    ) -> SpannedEncodingResult<()> {
        let assert_statement = self.encoder.set_statement_error_ctxt(
            vir_high::Statement::assert_no_pos(vir_high::Expression::builtin_func_app_no_pos(
                vir_high::BuiltinFunc::LifetimeIncluded,
                vec![], // NOTE: we ignore argument_types for LifetimeIncluded
                vec![
                    vir_high::VariableDecl {
                        name: lifetime_rhs,
                        ty: vir_high::ty::Type::Lifetime,
                    }
                    .into(),
                    vir_high::VariableDecl {
                        name: lifetime_lhs,
                        ty: vir_high::ty::Type::Lifetime,
                    }
                    .into(),
                ],
                vir_high::ty::Type::Bool,
            )),
            self.mir.span,
            ErrorCtxt::LifetimeEncoding,
            self.def_id,
        )?;
        block_builder.add_statement(self.set_statement_error(
            location,
            ErrorCtxt::LifetimeEncoding,
            assert_statement,
        )?);
        Ok(())
    }

    fn encode_lft_variable(
        &self,
        variable_name: String,
    ) -> SpannedEncodingResult<vir_high::VariableDecl> {
        Ok(vir_high::VariableDecl::new(
            variable_name,
            vir_high::Type::Lifetime,
        ))
    }

    /// A lifetime can be returned if:
    ///  - it is not present anymore
    ///  - the lifetimes it depends on have changed
    fn lifetimes_to_return(
        &mut self,
        old_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
    ) -> BTreeMap<String, BTreeSet<String>> {
        let mut derived_lifetimes_return: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for (lft, old_values) in old_derived_lifetimes.clone() {
            if !new_derived_lifetimes.contains_key(&lft) {
                derived_lifetimes_return.insert(lft.clone(), old_values.clone());
            } else {
                let new_values = new_derived_lifetimes.get(&lft).unwrap().clone();
                if old_values != new_values {
                    derived_lifetimes_return.insert(lft.clone(), old_values.clone());
                }
            }
        }
        derived_lifetimes_return
    }

    /// A lifetime can be taken if:
    ///  - it was newly introduced
    ///  - the lifetimes it depends on have changed
    fn lifetimes_to_take(
        &mut self,
        old_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
    ) -> BTreeMap<String, BTreeSet<String>> {
        let mut derived_lifetimes_take: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for (lft, new_values) in new_derived_lifetimes.clone() {
            if !old_derived_lifetimes.contains_key(&lft) {
                derived_lifetimes_take.insert(lft.clone(), new_values.clone());
            } else {
                let old_values = old_derived_lifetimes.get(&lft).unwrap().clone();
                if old_values != new_values {
                    derived_lifetimes_take.insert(lft.clone(), new_values.clone());
                }
            }
        }
        derived_lifetimes_take
    }

    fn lifetimes_to_end(
        &mut self,
        old_original_lifetimes: &BTreeSet<String>,
        new_original_lifetimes: &BTreeSet<String>,
    ) -> BTreeSet<String> {
        old_original_lifetimes
            .clone()
            .into_iter()
            .filter(|x| !new_original_lifetimes.contains(x))
            .collect()
    }

    fn lifetimes_to_create(
        &mut self,
        old_original_lifetimes: &BTreeSet<String>,
        new_original_lifetimes: &BTreeSet<String>,
    ) -> BTreeSet<String> {
        new_original_lifetimes
            .clone()
            .into_iter()
            .filter(|x| !old_original_lifetimes.contains(x))
            .collect()
    }

    fn lifetime_token_fractional_permission(&self, denominator: usize) -> vir_high::Expression {
        let denominator_expr = vir_high::Expression::constant_no_pos(
            vir_high::expression::ConstantValue::BigInt(denominator.to_string()),
            vir_high::ty::Type::MPerm,
        );
        vir_high::Expression::binary_op_no_pos(
            vir_high::BinaryOpKind::Div,
            self.lifetime_token_permission.clone().unwrap().into(),
            denominator_expr,
        )
    }

    fn encode_lifetime_specifications(
        &mut self,
    ) -> SpannedEncodingResult<(Vec<vir_high::Statement>, Vec<vir_high::Statement>)> {
        let mut preconditions = vec![vir_high::Statement::comment(
            "Lifetime preconditions.".to_string(),
        )];
        // Make sure the lifetime_token_permissino is > none and < write
        let none_permission = vir_high::Expression::none_permission();
        let full_permission = vir_high::Expression::full_permission();
        preconditions.push(self.encoder.set_statement_error_ctxt(
            vir_high::Statement::assume_no_pos(vir_high::Expression::binary_op_no_pos(
                vir_high::BinaryOpKind::GtCmp,
                self.lifetime_token_permission.clone().unwrap().into(),
                none_permission,
            )),
            self.mir.span,
            ErrorCtxt::LifetimeInhale,
            self.def_id,
        )?);
        preconditions.push(self.encoder.set_statement_error_ctxt(
            vir_high::Statement::assume_no_pos(vir_high::Expression::binary_op_no_pos(
                vir_high::BinaryOpKind::LtCmp,
                self.lifetime_token_permission.clone().unwrap().into(),
                full_permission,
            )),
            self.mir.span,
            ErrorCtxt::LifetimeInhale,
            self.def_id,
        )?);

        // Precondition: Inhale LifetimeTokens
        let lifetimes_to_inhale = self.opaque_lifetimes()?;
        for lifetime in &lifetimes_to_inhale {
            let inhale_statement = self.encode_inhale_lifetime_token(
                lifetime.clone(),
                self.lifetime_token_permission.clone().unwrap().into(),
            )?;
            preconditions.push(inhale_statement);
        }
        // Precondition: take lifetimes.
        let first_location = mir::Location {
            block: mir::START_BLOCK,
            statement_index: 0,
        };
        let derived_lifetimes = self
            .lifetimes
            .get_origin_contains_loan_at_start(first_location);
        for (derived, opaque) in &derived_lifetimes {
            // TODO: Remove duplication with encode_lft_take and encode_lft_return
            let encoded_target = self.encode_lft_variable(derived.clone())?;
            let mut lifetimes: Vec<vir_high::VariableDecl> = Vec::new();
            assert!(!opaque.is_empty());
            for lifetime_name in opaque {
                lifetimes.push(self.encode_lft_variable(lifetime_name.clone())?);
            }
            preconditions.push(self.encoder.set_statement_error_ctxt(
                vir_high::Statement::lifetime_take_no_pos(
                    encoded_target,
                    lifetimes,
                    self.lifetime_token_fractional_permission(self.lifetime_count),
                ),
                self.mir.span,
                ErrorCtxt::LifetimeEncoding,
                self.def_id,
            )?);
        }

        // Postcondition: Exhale (inhaled) LifetimeTokens
        let mut postconditions = vec![vir_high::Statement::comment(
            "Lifetime postconditions.".to_string(),
        )];
        for (derived, opaque) in &derived_lifetimes {
            // TODO: Remove duplication with encode_lft_take and encode_lft_return
            let encoded_target = self.encode_lft_variable(derived.clone())?;
            let mut lifetimes: Vec<vir_high::VariableDecl> = Vec::new();
            assert!(!opaque.is_empty());
            for lifetime_name in opaque {
                lifetimes.push(self.encode_lft_variable(lifetime_name.clone())?);
            }
            postconditions.push(self.encoder.set_statement_error_ctxt(
                vir_high::Statement::lifetime_return_no_pos(
                    encoded_target,
                    lifetimes,
                    self.lifetime_token_fractional_permission(self.lifetime_count),
                ),
                self.mir.span,
                ErrorCtxt::LifetimeEncoding,
                self.def_id,
            )?);
        }
        for lifetime in lifetimes_to_inhale {
            let exhale_statement = self.encode_exhale_lifetime_token(
                lifetime,
                self.lifetime_token_permission.clone().unwrap().into(),
            )?;
            postconditions.push(exhale_statement);
        }

        Ok((preconditions, postconditions))
    }

    fn identical_lifetimes_map(
        &mut self,
        existing_lifetimes: BTreeSet<String>,
        relations: BTreeSet<(String, String)>,
    ) -> BTreeMap<String, String> {
        let unique_lifetimes: BTreeSet<String> = relations
            .iter()
            .flat_map(|(x, y)| [x, y])
            .cloned()
            .collect();
        let n = unique_lifetimes.len();
        let mut lft_enumarate: BTreeMap<String, usize> = BTreeMap::new();
        let mut lft_enumarate_rev: BTreeMap<usize, String> = BTreeMap::new();

        for (i, e) in unique_lifetimes.iter().enumerate() {
            lft_enumarate.insert(e.to_string(), i);
            lft_enumarate_rev.insert(i, e.to_string());
        }

        let graph = {
            let mut g = Graph::new(n);
            for (k, v) in relations {
                g.add_edge(
                    *lft_enumarate.get(&k[..]).unwrap(),
                    *lft_enumarate.get(&v[..]).unwrap(),
                );
            }
            g
        };

        // compute strongly connected components
        let mut identical_lifetimes: BTreeSet<BTreeSet<String>> = BTreeSet::new();
        for component in Tarjan::walk(&graph) {
            identical_lifetimes.insert(
                component
                    .iter()
                    .map(|x| lft_enumarate_rev.get(x).unwrap())
                    .cloned()
                    .collect(),
            );
        }

        // put data in correct shape
        let mut identical_lifetimes_map: BTreeMap<String, String> = BTreeMap::new();
        for component in identical_lifetimes {
            let existing_component_lifetims: BTreeSet<String> = component
                .iter()
                .filter(|lft| existing_lifetimes.contains(&lft[..]))
                .cloned()
                .collect();
            let non_existing_component_lifetimes: BTreeSet<String> = component
                .iter()
                .filter(|lft| !existing_lifetimes.contains(&lft[..]))
                .cloned()
                .collect();
            for lifetime in non_existing_component_lifetimes {
                let identical_existing_lifetime = existing_component_lifetims.iter().next();
                if let Some(identical_existing_lifetime) = identical_existing_lifetime {
                    identical_lifetimes_map.insert(lifetime, identical_existing_lifetime.clone());
                } else {
                    // FIXME: Some programs produce lots of identical and seemingly useless lifetimes
                    //   for example: main(){ let x: &mut u32 = &mut 0; }
                    //   currently, we ignore them
                }
            }
        }
        identical_lifetimes_map
    }

    fn opaque_lifetimes(&mut self) -> SpannedEncodingResult<Vec<vir_high::ty::LifetimeConst>> {
        Ok(self
            .lifetimes
            .get_opaque_lifetimes_with_names()
            .into_iter()
            .map(vir_high::ty::LifetimeConst::new)
            .collect())
    }

    fn encode_inhale_lifetime_token(
        &mut self,
        lifetime_const: vir_high::ty::LifetimeConst,
        permission_amount: vir_high::Expression,
    ) -> SpannedEncodingResult<vir_high::Statement> {
        self.encoder.set_statement_error_ctxt(
            vir_high::Statement::inhale_no_pos(vir_high::Predicate::lifetime_token_no_pos(
                lifetime_const,
                permission_amount,
            )),
            self.mir.span,
            ErrorCtxt::LifetimeInhale,
            self.def_id,
        )
    }

    fn encode_inhale_lifetime_tokens(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        lifetime_names: &[String],
        permission_divisor_mult: usize,
    ) -> SpannedEncodingResult<()> {
        for lifetime in lifetime_names {
            let statement = self.encode_inhale_lifetime_token(
                vir_high::ty::LifetimeConst {
                    name: lifetime.clone(),
                },
                self.lifetime_token_fractional_permission(
                    self.lifetime_count * permission_divisor_mult,
                ),
            )?;
            block_builder.add_statement(statement);
        }
        Ok(())
    }

    fn encode_exhale_lifetime_token(
        &mut self,
        lifetime_const: vir_high::ty::LifetimeConst,
        permission_amount: vir_high::Expression,
    ) -> SpannedEncodingResult<vir_high::Statement> {
        self.encoder.set_statement_error_ctxt(
            vir_high::Statement::exhale_no_pos(vir_high::Predicate::lifetime_token_no_pos(
                lifetime_const,
                permission_amount,
            )),
            self.mir.span,
            ErrorCtxt::LifetimeExhale,
            self.def_id,
        )
    }

    fn encode_exhale_lifetime_tokens(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        lifetime_names: &[String],
        permission_divisor_mult: usize,
    ) -> SpannedEncodingResult<()> {
        for lifetime in lifetime_names {
            let statement = self.encode_exhale_lifetime_token(
                vir_high::ty::LifetimeConst {
                    name: lifetime.clone(),
                },
                self.lifetime_token_fractional_permission(
                    self.lifetime_count * permission_divisor_mult,
                ),
            )?;
            block_builder.add_statement(statement);
        }
        Ok(())
    }
}
