//! Code for converting variables to SSA form.

use super::*;
use std::collections::BTreeMap;

/// `BBI` is basic block ID.
pub struct SSAState<BBI> {
    all_variables: AllVariablesMap,
    variables: BTreeMap<BBI, VariableVersionMap>,
    variables_at_label: BTreeMap<String, VariableVersionMap>,
    current_variables: Option<VariableVersionMap>,
}

impl<BBI> Default for SSAState<BBI> {
    fn default() -> Self {
        Self {
            all_variables: Default::default(),
            variables: Default::default(),
            variables_at_label: Default::default(),
            current_variables: Default::default(),
        }
    }
}

impl<BBI: Ord + Clone + std::fmt::Debug> SSAState<BBI> {
    pub fn initial_variable_version(&self, _variable_name: &str) -> u64 {
        0
    }

    pub fn new_variable_version(
        &mut self,
        variable_name: &str,
        ty: &Type,
        position: Position,
    ) -> u64 {
        let new_version = self
            .all_variables
            .new_version_or_default(variable_name, ty, position);
        self.current_variables
            .as_mut()
            .unwrap()
            .set(variable_name.to_string(), new_version);
        new_version
    }

    pub fn current_variable_version(&self, variable_name: &str) -> u64 {
        self.current_variables
            .as_ref()
            .expect("make sure to call prepare_new_current_block")
            .get_or_default(variable_name)
    }

    pub fn variable_version_at_label(&self, variable_name: &str, label: &str) -> u64 {
        self.variables_at_label
            .get(label)
            .unwrap_or_else(|| panic!("not found label {label}"))
            .get_or_default(variable_name)
    }

    pub fn variable_version_at_maybe_label(
        &self,
        variable_name: &str,
        label: &Option<String>,
    ) -> u64 {
        if let Some(label) = label {
            self.variable_version_at_label(variable_name, label)
        } else {
            self.current_variable_version(variable_name)
        }
    }

    /// Set the specified block as current and compute the SSA versions of all
    /// incoming variables. This method assumes that all predecessors are
    /// already analysed.
    pub fn prepare_new_current_block(
        &mut self,
        label: &BBI,
        predecessors: &BTreeMap<BBI, Vec<BBI>>,
        basic_block_edges: &mut BTreeMap<
            BBI,
            BTreeMap<BBI, Vec<(String, Type, Position, u64, u64)>>,
        >,
    ) {
        assert!(self.current_variables.is_none());
        let predecessor_labels = &predecessors[label];
        let predecessor_maps = predecessor_labels
            .iter()
            .map(|label| &self.variables[label])
            .collect::<Vec<_>>();
        let mut new_map = VariableVersionMap::default();
        for variable in self.all_variables.names_clone() {
            let first_version = predecessor_maps
                .get(0)
                .unwrap_or_else(|| panic!("for label {label:?} predecessors: {predecessors:?}"))
                .get_or_default(&variable);
            let different = predecessor_maps
                .iter()
                .any(|map| map.get_or_default(&variable) != first_version);
            if different {
                let new_version = self.all_variables.new_version(&variable);
                let ty = self.all_variables.get_type(&variable).clone();
                for predecessor_label in predecessor_labels {
                    let old_version = self.variables[predecessor_label].get_or_default(&variable);
                    let statements = basic_block_edges
                        .entry(predecessor_label.clone())
                        .or_default()
                        .entry(label.clone())
                        .or_default();
                    let position = self.all_variables.get_position(&variable);
                    let statement = (
                        variable.clone(),
                        ty.clone(),
                        position,
                        old_version,
                        new_version,
                    );
                    statements.push(statement);
                }
                new_map.set(variable, new_version);
            } else {
                new_map.set(variable, first_version);
            }
        }
        self.current_variables = Some(new_map);
    }

    pub fn finish_current_block(&mut self, label: BBI) {
        let current_variables = self.current_variables.take().unwrap();
        assert!(self.variables.insert(label, current_variables).is_none());
    }

    pub fn save_state_at_label(&mut self, label: String) {
        let current_variables = self.current_variables.clone().unwrap();
        assert!(self
            .variables_at_label
            .insert(label, current_variables)
            .is_none());
    }

    pub fn change_state_to_label(&mut self, label: &str) {
        self.current_variables = Some(self.variables_at_label[label].clone());
    }
}

#[derive(Default, Clone)]
pub struct VariableVersionMap {
    /// Mapping from variable names to their versions.
    variable_versions: BTreeMap<String, u64>,
}

impl std::fmt::Display for VariableVersionMap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{{")?;
        for (variable_name, version) in &self.variable_versions {
            writeln!(f, "{variable_name}: {version}")?;
        }
        writeln!(f, "}}")?;
        Ok(())
    }
}

impl VariableVersionMap {
    pub fn get_or_default(&self, variable: &str) -> u64 {
        self.variable_versions.get(variable).cloned().unwrap_or(0)
    }
    pub fn set(&mut self, variable: String, version: u64) {
        self.variable_versions.insert(variable, version);
    }
}

#[derive(Default)]
pub struct AllVariablesMap {
    versions: BTreeMap<String, u64>,
    types: BTreeMap<String, Type>,
    positions: BTreeMap<String, Position>,
}

impl AllVariablesMap {
    pub fn names_clone(&self) -> Vec<String> {
        self.versions.keys().cloned().collect()
    }
    pub fn get_type(&self, variable: &str) -> &Type {
        &self.types[variable]
    }
    pub fn get_position(&self, variable: &str) -> Position {
        self.positions[variable]
    }
    pub fn new_version(&mut self, variable: &str) -> u64 {
        let current_version = self.versions.get_mut(variable).unwrap();
        *current_version += 1;
        *current_version
    }
    pub fn new_version_or_default(&mut self, variable: &str, ty: &Type, position: Position) -> u64 {
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
