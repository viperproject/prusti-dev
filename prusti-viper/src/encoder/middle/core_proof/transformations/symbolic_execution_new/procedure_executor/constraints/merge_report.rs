use rustc_hash::FxHashMap;
use std::collections::BTreeMap;
use vir_crate::low::{self as vir_low};

#[derive(Debug, Clone)]
pub(in super::super) struct ConstraintsMergeReport {
    // pub(super) dropped_self_lifetime_equalities: BTreeMap<String, String>,
    // pub(super) dropped_other_lifetime_equalities: BTreeMap<String, String>,
    pub(super) self_lifetime_version_updates: BTreeMap<(String, u32), u32>,
    pub(super) other_lifetime_version_updates: BTreeMap<(String, u32), u32>,
    pub(super) self_remaps: FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl>,
    pub(super) other_remaps: FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl>,
    pub(super) dropped_self_equalities: FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl>,
    pub(super) dropped_other_equalities: FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl>,
}

impl ConstraintsMergeReport {
    // pub(in super::super) fn resolve_new_self_cannonical_lifetime_name(
    //     &self,
    //     lifetime_name: &str,
    // ) -> Option<&String> {
    //     self.dropped_self_lifetime_equalities.get(lifetime_name)
    // }

    // pub(in super::super) fn resolve_new_other_cannonical_lifetime_name(
    //     &self,
    //     lifetime_name: &str,
    // ) -> Option<&String> {
    //     self.dropped_other_lifetime_equalities.get(lifetime_name)
    // }

    // pub(in super::super) fn resolve_old_other_cannonical_lifetime_name(
    //     &self,
    //     lifetime_name: &str,
    // ) -> Option<&String> {
    //     self.dropped_other_lifetime_equalities
    //         .iter()
    //         .find_map(|(old_name, new_name)| {
    //             if new_name == lifetime_name {
    //                 Some(old_name)
    //             } else {
    //                 None
    //             }
    //         })
    // }

    pub(in super::super) fn resolve_self_latest_lifetime_variable_version(
        &self,
        lifetime_variable: &str,
        mut current_version: u32,
    ) -> u32 {
        while let Some(new_version) = self
            .self_lifetime_version_updates
            .get(&(lifetime_variable.to_string(), current_version))
            .copied()
        {
            current_version = new_version;
        }
        current_version
    }

    pub(in super::super) fn resolve_other_latest_lifetime_variable_version(
        &self,
        lifetime_variable: &str,
        mut current_version: u32,
    ) -> u32 {
        while let Some(new_version) = self
            .other_lifetime_version_updates
            .get(&(lifetime_variable.to_string(), current_version))
            .copied()
        {
            current_version = new_version;
        }
        current_version
        // self.other_lifetime_version_updates
        //     .get(&(lifetime_variable.to_string(), current_version))
        //     .copied()
        //     .unwrap_or(current_version)
    }

    pub(in super::super) fn get_self_remaps(
        &self,
    ) -> &FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl> {
        &self.self_remaps
    }

    pub(in super::super) fn get_other_remaps(
        &self,
    ) -> &FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl> {
        &self.other_remaps
    }

    pub(in super::super) fn get_dropped_self_equalities(
        &self,
    ) -> &FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl> {
        &self.dropped_self_equalities
    }

    pub(in super::super) fn get_dropped_other_equalities(
        &self,
    ) -> &FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl> {
        &self.dropped_other_equalities
    }
}
