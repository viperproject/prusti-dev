use super::GlobalHeapState;
use std::collections::BTreeSet;
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low},
};

// FIXME: Rename to `HeapMergeState`.
#[derive(Debug, Clone)]
pub(in super::super) struct HeapMergeReport {
    snapshot_report: Report<SnapshotRemap>,
    permission_report: Report<PermissionRemap>,
    new_dead_lifetime_token_permission_map: Option<vir_low::Expression>,
    old_permission_maps: Vec<vir_low::Expression>,
    /// For each predecessor, a list of permission variables that got `write`
    /// assigned to them.
    write_written_in_predecessors: Vec<Vec<vir_low::VariableDecl>>,
}

#[derive(Debug, Clone, Default)]
struct Report<Remap> {
    predecessors: Vec<HeapMergePredecessorReport<Remap>>,
}

#[derive(Debug, Clone)]
struct HeapMergePredecessorReport<Remap> {
    remaps: Vec<Remap>,
}

impl<Remap> Default for HeapMergePredecessorReport<Remap> {
    fn default() -> Self {
        Self { remaps: Vec::new() }
    }
}

#[derive(Debug, Clone)]
pub(in super::super) struct SnapshotRemap {
    old_snapshot: String,
    new_snapshot: String,
    ty: vir_low::Type,
}

#[derive(Debug, Clone)]
pub(in super::super) struct PermissionRemap {
    old_snapshot: String,
    new_snapshot: String,
}

trait Remap {
    fn create(old: &vir_low::VariableDecl, new: String) -> Self;
    fn old(&self) -> &str;
    fn new(&self) -> &str;
    fn create_variable(
        global_stae: &mut GlobalHeapState,
        predicate_name: &str,
        ty: &vir_low::Type,
    ) -> vir_low::VariableDecl;
}

impl Remap for SnapshotRemap {
    fn create(old: &vir_low::VariableDecl, new: String) -> Self {
        Self {
            old_snapshot: old.name.clone(),
            new_snapshot: new,
            ty: old.ty.clone(),
        }
    }

    fn old(&self) -> &str {
        &self.old_snapshot
    }

    fn new(&self) -> &str {
        &self.new_snapshot
    }

    fn create_variable(
        global_state: &mut GlobalHeapState,
        predicate_name: &str,
        ty: &vir_low::Type,
    ) -> vir_low::VariableDecl {
        global_state.create_snapshot_variable(predicate_name, ty.clone())
    }
}

impl Remap for PermissionRemap {
    fn create(old: &vir_low::VariableDecl, new: String) -> Self {
        Self {
            old_snapshot: old.name.clone(),
            new_snapshot: new,
        }
    }

    fn old(&self) -> &str {
        &self.old_snapshot
    }

    fn new(&self) -> &str {
        &self.new_snapshot
    }

    fn create_variable(
        global_state: &mut GlobalHeapState,
        predicate_name: &str,
        _: &vir_low::Type,
    ) -> vir_low::VariableDecl {
        global_state.create_permission_variable(predicate_name)
    }
}

impl<R: Remap> Report<R> {
    fn new() -> Self {
        Self {
            predecessors: vec![HeapMergePredecessorReport::default()],
        }
    }

    fn create_predecessor(&mut self) {
        self.predecessors
            .push(HeapMergePredecessorReport::default());
    }

    fn remap(
        &mut self,
        predicate_name: &str,
        self_variable: &vir_low::VariableDecl,
        other_variable: &vir_low::VariableDecl,
        global_state: &mut GlobalHeapState,
    ) -> vir_low::VariableDecl {
        assert!(self.predecessors.len() >= 2);
        let new_variable = if let Some(new_variable_name) = self.has_remap(self_variable) {
            self.remap_last_predecessor(other_variable, new_variable_name.to_string())
        } else {
            self.create_remap(predicate_name, self_variable, other_variable, global_state)
        };
        new_variable
    }

    fn has_remap(&self, first_predecessor_variable: &vir_low::VariableDecl) -> Option<&str> {
        for remap in &self.predecessors[0].remaps {
            if remap.new() == first_predecessor_variable.name {
                return Some(&remap.new());
            }
        }
        None
    }

    fn remap_last_predecessor(
        &mut self,
        last_predecessor_variable: &vir_low::VariableDecl,
        new_variable: String,
    ) -> vir_low::VariableDecl {
        let last_predecessor = self.predecessors.last_mut().unwrap();
        last_predecessor.remaps.push(Remap::create(
            &last_predecessor_variable,
            new_variable.clone(),
        ));
        vir_low::VariableDecl {
            name: new_variable,
            ty: last_predecessor_variable.ty.clone(),
        }
    }

    fn create_remap(
        &mut self,
        predicate_name: &str,
        first_predecessor_variable: &vir_low::VariableDecl,
        last_predecessor_variable: &vir_low::VariableDecl,
        global_state: &mut GlobalHeapState,
    ) -> vir_low::VariableDecl {
        let variable =
            R::create_variable(global_state, predicate_name, &first_predecessor_variable.ty);
        for i in 0..self.predecessors.len() - 1 {
            self.predecessors[i].remaps.push(Remap::create(
                &first_predecessor_variable,
                variable.name.clone(),
            ));
        }
        let last_index = self.predecessors.len() - 1;
        self.predecessors[last_index].remaps.push(Remap::create(
            &last_predecessor_variable,
            variable.name.clone(),
        ));
        variable
    }

    fn validate(&self) {
        let mut new_variables = BTreeSet::new();
        for remap in &self.predecessors[0].remaps {
            assert!(new_variables.insert(remap.new()), "{}", remap.new());
        }
        for (_i, predecessor) in self.predecessors.iter().enumerate() {
            // This does not hold because some of the incoming paths may
            // completely miss the resources.
            // assert_eq!(predecessor.remaps.len(), new_variables.len(), "{}", i);
            for remap in &predecessor.remaps {
                assert!(new_variables.contains(&remap.new()));
            }
        }
    }

    pub(in super::super) fn into_iter_remap(self) -> impl Iterator<Item = Vec<R>> {
        self.predecessors
            .into_iter()
            .map(|predecessor| predecessor.remaps)
    }
}

impl HeapMergeReport {
    pub(in super::super) fn new() -> Self {
        Self {
            snapshot_report: Report::new(),
            permission_report: Report::new(),
            new_dead_lifetime_token_permission_map: None,
            old_permission_maps: Vec::new(),
            write_written_in_predecessors: vec![Vec::new()],
        }
    }

    pub(in super::super) fn create_predecessor(&mut self) {
        self.snapshot_report.create_predecessor();
        self.permission_report.create_predecessor();
        self.write_written_in_predecessors.push(Vec::new());
    }

    pub(in super::super) fn is_new_dead_lifetime_token_permission_map_set(&self) -> bool {
        self.new_dead_lifetime_token_permission_map.is_some()
    }

    pub(in super::super) fn set_new_dead_lifetime_token_permission_map(
        &mut self,
        new_map: vir_low::Expression,
    ) {
        assert!(self.new_dead_lifetime_token_permission_map.is_none());
        self.new_dead_lifetime_token_permission_map = Some(new_map);
    }

    pub(in super::super) fn add_old_permission_map(&mut self, old_map: vir_low::Expression) {
        self.old_permission_maps.push(old_map);
    }

    pub(in super::super) fn remap_snapshot_variable(
        &mut self,
        predicate_name: &str,
        self_snapshot_variable: &vir_low::VariableDecl,
        other_snapshot_variable: &vir_low::VariableDecl,
        global_state: &mut GlobalHeapState,
    ) -> vir_low::VariableDecl {
        self.snapshot_report.remap(
            predicate_name,
            self_snapshot_variable,
            other_snapshot_variable,
            global_state,
        )
    }

    pub(in super::super) fn remap_permission_variable(
        &mut self,
        predicate_name: &str,
        self_permission_variable: &vir_low::VariableDecl,
        other_permission_variable: &vir_low::VariableDecl,
        global_state: &mut GlobalHeapState,
    ) -> vir_low::VariableDecl {
        self.permission_report.remap(
            predicate_name,
            self_permission_variable,
            other_permission_variable,
            global_state,
        )
    }

    pub(in super::super) fn set_write_in_all_predecessors_except_last(
        &mut self,
        variable: &vir_low::VariableDecl,
    ) {
        let len = self.write_written_in_predecessors.len() - 1;
        for predecessor in &mut self.write_written_in_predecessors[..len] {
            predecessor.push(variable.clone());
        }
    }

    pub(in super::super) fn set_write_in_last_predecessor(
        &mut self,
        variable: vir_low::VariableDecl,
    ) {
        let len = self.write_written_in_predecessors.len();
        self.write_written_in_predecessors[len - 1].push(variable);
    }

    pub(in super::super) fn validate(&self) {
        self.snapshot_report.validate();
        self.permission_report.validate();
    }

    pub(in super::super) fn into_remap_statements(
        self,
        position: vir_low::Position,
    ) -> Vec<Vec<vir_low::Statement>> {
        assert_eq!(
            self.snapshot_report.predecessors.len(),
            self.permission_report.predecessors.len()
        );
        assert_eq!(
            self.snapshot_report.predecessors.len(),
            self.write_written_in_predecessors.len()
        );
        let mut predecessor_statements = Vec::new();
        // let new_dead_lifetime_token_permission_map =
        //     self.new_dead_lifetime_token_permission_map.unwrap();
        // for ((snapshot_remaps, permission_remaps), old_permission_map) in self
        // for (snapshot_remaps, permission_remaps) in self
        for ((snapshot_remaps, permission_remaps), written_write) in self
            .snapshot_report
            .into_iter_remap()
            .zip(self.permission_report.into_iter_remap())
            .zip(self.write_written_in_predecessors.into_iter())
        // .zip(self.old_permission_maps)
        {
            let mut statements_for_predecessor = Vec::new();
            for snapshot_remap in snapshot_remaps {
                statements_for_predecessor.push(snapshot_remap.into_assume_statement(position));
            }
            for permission_remap in permission_remaps {
                statements_for_predecessor.push(permission_remap.into_assign_statement(position));
            }
            for variable in written_write {
                statements_for_predecessor.push(
                    vir_low::Statement::assign_no_pos(
                        variable,
                        vir_low::Expression::full_permission(),
                    )
                    .set_default_position(position),
                );
            }
            // statements_for_predecessor.push(
            //     vir_low::Statement::assume_no_pos(vir_low::Expression::equals(
            //         new_dead_lifetime_token_permission_map.clone(),
            //         old_permission_map,
            //     ))
            //     .set_default_position(position),
            // );
            predecessor_statements.push(statements_for_predecessor);
        }
        predecessor_statements
    }
}

impl SnapshotRemap {
    /// Snapshots are in SSA, so we can use assume statements to remap them.
    pub(in super::super) fn into_assume_statement(
        self,
        position: vir_low::Position,
    ) -> vir_low::Statement {
        vir_low::Statement::assume_no_pos(vir_low::Expression::equals(
            vir_low::VariableDecl::new(self.old_snapshot, self.ty.clone()).into(),
            vir_low::VariableDecl::new(self.new_snapshot, self.ty).into(),
        ))
        .set_default_position(position)
    }
}

impl PermissionRemap {
    /// Permissions are not in SSA, so we need to use assign to remap them.
    pub(in super::super) fn into_assign_statement(
        self,
        position: vir_low::Position,
    ) -> vir_low::Statement {
        vir_low::Statement::assign_no_pos(
            vir_low::VariableDecl::new(self.new_snapshot, vir_low::Type::Perm),
            vir_low::VariableDecl::new(self.old_snapshot, vir_low::Type::Perm).into(),
        )
        .set_default_position(position)
    }
}
