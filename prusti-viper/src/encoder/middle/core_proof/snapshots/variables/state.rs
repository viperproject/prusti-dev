use std::collections::BTreeMap;
use vir_crate::low::{self as vir_low};

#[derive(Default, Clone)]
pub(in super::super::super) struct VariableVersionMap {
    /// Mapping from variable names to their versions.
    variable_versions: BTreeMap<String, u64>,
}

impl std::fmt::Display for VariableVersionMap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{{")?;
        for (variable_name, version) in &self.variable_versions {
            writeln!(f, "{}: {}", variable_name, version)?;
        }
        writeln!(f, "}}")?;
        Ok(())
    }
}

impl VariableVersionMap {
    pub(super) fn get_or_default(&self, variable: &str) -> u64 {
        self.variable_versions.get(variable).cloned().unwrap_or(0)
    }
    pub(super) fn set(&mut self, variable: String, version: u64) {
        self.variable_versions.insert(variable, version);
    }
}

#[derive(Default)]
pub(in super::super::super) struct AllVariablesMap {
    versions: BTreeMap<String, u64>,
    types: BTreeMap<String, vir_low::Type>,
    positions: BTreeMap<String, vir_low::Position>,
}

impl AllVariablesMap {
    pub(super) fn names_clone(&self) -> Vec<String> {
        self.versions.keys().cloned().collect()
    }
    pub(super) fn get_type(&self, variable: &str) -> &vir_low::Type {
        &self.types[variable]
    }
    pub(super) fn get_position(&self, variable: &str) -> vir_low::Position {
        self.positions[variable]
    }
    pub(super) fn new_version(&mut self, variable: &str) -> u64 {
        let current_version = self.versions.get_mut(variable).unwrap();
        *current_version += 1;
        *current_version
    }
    pub(super) fn new_version_or_default(
        &mut self,
        variable: &str,
        ty: &vir_low::Type,
        position: vir_low::Position,
    ) -> u64 {
        if self.versions.contains_key(variable) {
            let version = self.versions.get_mut(variable).unwrap();
            *version += 1;
            *version
        } else {
            self.versions.insert(variable.to_string(), 1);
            self.types.insert(variable.to_string(), ty.clone());
            self.positions.insert(variable.to_string(), position);
            1
        }
    }
}
