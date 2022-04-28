use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    mir::procedures::encoder::ProcedureEncoder,
};
use rustc_middle::mir;
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::high::{self as vir_high, builders::procedure::BasicBlockBuilder};

pub(super) trait LifetimesEncoder {
    fn encode_lft_for_statement(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        original_lifetimes: &mut BTreeSet<String>,
        derived_lifetimes: &mut BTreeMap<String, BTreeSet<String>>,
    ) -> SpannedEncodingResult<()>;
    fn encode_lft_for_block(
        &mut self,
        target: mir::BasicBlock,
        location: mir::Location,
        block_builder: &mut BasicBlockBuilder,
    ) -> SpannedEncodingResult<()>;
    fn encode_lft(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        old_original_lifetimes: &mut BTreeSet<String>,
        old_derived_lifetimes: &mut BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
    ) -> SpannedEncodingResult<()>;
    fn encode_dead_variables(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        old_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
    ) -> SpannedEncodingResult<()>;
    fn encode_new_lft(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        old_original_lifetimes: &BTreeSet<String>,
        new_original_lifetimes: &BTreeSet<String>,
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
    ) -> SpannedEncodingResult<()>;
    fn encode_lft_variable(
        &self,
        variable_name: String,
    ) -> SpannedEncodingResult<vir_high::VariableDecl>;
    fn variables_to_kill(
        &mut self,
        old_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
    ) -> SpannedEncodingResult<BTreeSet<vir_high::Local>>;
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
}

impl<'p, 'v: 'p, 'tcx: 'v> LifetimesEncoder for ProcedureEncoder<'p, 'v, 'tcx> {
    fn encode_lft_for_statement(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        original_lifetimes: &mut BTreeSet<String>,
        derived_lifetimes: &mut BTreeMap<String, BTreeSet<String>>,
    ) -> SpannedEncodingResult<()> {
        let new_derived_lifetimes = self.lifetimes.get_origin_contains_loan_at_mid(location);
        block_builder.add_comment(format!("Prepare lifetimes for statement {:?}", location));
        self.encode_lft(
            block_builder,
            location,
            original_lifetimes,
            derived_lifetimes,
            &new_derived_lifetimes,
        )?;
        Ok(())
    }

    fn encode_lft_for_block(
        &mut self,
        target: mir::BasicBlock,
        location: mir::Location,
        block_builder: &mut BasicBlockBuilder,
    ) -> SpannedEncodingResult<()> {
        let needed_derived_lifetimes = self.needed_derived_lifetimes_for_block(&target);
        let mut current_derived_lifetimes =
            self.lifetimes.get_origin_contains_loan_at_mid(location);
        let mut current_original_lifetimes = self.lifetimes.get_loan_live_at_start(location);
        block_builder.add_comment(format!("Prepare lifetimes for block {:?}", target));
        self.encode_lft(
            block_builder,
            location,
            &mut current_original_lifetimes,
            &mut current_derived_lifetimes,
            &needed_derived_lifetimes,
        )?;
        Ok(())
    }

    /// Adds all statements needed for the encoding of the location.
    fn encode_lft(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        old_original_lifetimes: &mut BTreeSet<String>,
        old_derived_lifetimes: &mut BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
    ) -> SpannedEncodingResult<()> {
        let new_original_lifetimes: BTreeSet<String> = new_derived_lifetimes
            .clone()
            .into_values()
            .flatten()
            .collect();
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
        self.encode_dead_variables(
            block_builder,
            location,
            old_derived_lifetimes,
            new_derived_lifetimes,
        )?;
        self.encode_new_lft(
            block_builder,
            location,
            old_original_lifetimes,
            &new_original_lifetimes,
        )?;
        self.encode_lft_take(
            block_builder,
            location,
            old_derived_lifetimes,
            new_derived_lifetimes,
        )?;

        *old_original_lifetimes = new_original_lifetimes.clone();
        *old_derived_lifetimes = new_derived_lifetimes.clone();
        Ok(())
    }

    fn encode_dead_variables(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        old_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
    ) -> SpannedEncodingResult<()> {
        let variables_to_kill =
            self.variables_to_kill(old_derived_lifetimes, new_derived_lifetimes)?;
        for var in variables_to_kill {
            block_builder.add_statement(self.set_statement_error(
                location,
                ErrorCtxt::LifetimeEncoding,
                vir_high::Statement::dead_no_pos(var.into()),
            )?);
        }
        Ok(())
    }

    fn encode_new_lft(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        old_original_lifetimes: &BTreeSet<String>,
        new_original_lifetimes: &BTreeSet<String>,
    ) -> SpannedEncodingResult<()> {
        let lifetimes_to_create =
            self.lifetimes_to_create(old_original_lifetimes, new_original_lifetimes);
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
            let encoded_target = self.encode_lft_variable(lifetime)?;
            let mut lifetimes: Vec<vir_high::VariableDecl> = Vec::new();
            for lifetime_name in derived_from {
                lifetimes.push(self.encode_lft_variable(lifetime_name)?);
            }
            block_builder.add_statement(self.set_statement_error(
                location,
                ErrorCtxt::LifetimeEncoding,
                vir_high::Statement::lifetime_return_no_pos(
                    encoded_target,
                    lifetimes,
                    self.rd_perm,
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
    ) -> SpannedEncodingResult<()> {
        let lifetimes_to_take =
            self.lifetimes_to_take(old_derived_lifetimes, new_derived_lifetimes);
        for (lifetime, derived_from) in lifetimes_to_take {
            let encoded_target = self.encode_lft_variable(lifetime)?;
            let mut lifetimes: Vec<vir_high::VariableDecl> = Vec::new();
            for lifetime_name in derived_from {
                lifetimes.push(self.encode_lft_variable(lifetime_name)?);
            }
            block_builder.add_statement(self.set_statement_error(
                location,
                ErrorCtxt::LifetimeEncoding,
                vir_high::Statement::lifetime_take_no_pos(encoded_target, lifetimes, self.rd_perm),
            )?);
        }
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

    /// A variable can be killed if its lifetime was previously derived from lifetimes
    /// but isn't anymore now.
    fn variables_to_kill(
        &mut self,
        old_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
        new_derived_lifetimes: &BTreeMap<String, BTreeSet<String>>,
    ) -> SpannedEncodingResult<BTreeSet<vir_high::Local>> {
        let mut variables_to_kill = BTreeSet::new();
        for derived_lifetime in old_derived_lifetimes.keys() {
            if !new_derived_lifetimes.contains_key(derived_lifetime) {
                if let Some(local) = self.procedure.get_var_of_lifetime(&derived_lifetime[..]) {
                    variables_to_kill.insert(self.encode_local(local)?);
                }
            }
        }
        Ok(variables_to_kill)
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
}
