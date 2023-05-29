use super::{BlockHeap, HeapAtLabel};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::symbolic_execution_new::{
        expression_interner::ExpressionInterner, program_context::ProgramContext,
    },
};
use std::collections::BTreeMap;
use vir_crate::low::{self as vir_low};

#[derive(Default)]
pub(in super::super::super) struct GlobalHeapState {
    pub(super) snapshots_at_label: BTreeMap<String, HeapAtLabel>,
    pub(super) heap_variables: HeapVariables,
}

#[derive(Default)]
pub(in super::super::super) struct HeapVariables {
    variables: Vec<vir_low::VariableDecl>,
    /// NOTE: Permission variables are **NOT** SSA.
    permission_variables: Vec<vir_low::VariableDecl>,
    permission_map_variables: Vec<vir_low::VariableDecl>,
}

impl HeapVariables {
    pub(super) fn create_snapshot_variable(
        &mut self,
        predicate_name: &str,
        ty: vir_low::Type,
    ) -> vir_low::VariableDecl {
        let snapshot_variable_name =
            format!("snapshot${}${}", predicate_name, self.variables.len());
        let variable = vir_low::VariableDecl::new(snapshot_variable_name, ty);
        self.variables.push(variable.clone());
        variable
    }

    pub(super) fn create_merge_variable(&mut self, ty: vir_low::Type) -> vir_low::VariableDecl {
        let variable_name = format!("merge_variable${}", self.variables.len());
        let variable = vir_low::VariableDecl::new(variable_name, ty);
        self.variables.push(variable.clone());
        variable
    }

    /// Note: Permission variables are **NOT** SSA.
    pub(super) fn create_permission_variable(
        &mut self,
        predicate_name: &str,
    ) -> vir_low::VariableDecl {
        let permission_variable_name = format!(
            "permission${}${}",
            predicate_name,
            self.permission_variables.len()
        );
        let variable = vir_low::VariableDecl::new(permission_variable_name, vir_low::Type::Perm);
        self.permission_variables.push(variable.clone());
        variable
    }

    pub(in super::super::super) fn initialize_permission_variables(
        &self,
        position: vir_low::Position,
    ) -> impl Iterator<Item = vir_low::Statement> + '_ {
        self.permission_variables.iter().map(move |variable| {
            vir_low::Statement::assign_no_pos(
                variable.clone(),
                vir_low::Expression::no_permission(),
            )
            .set_default_position(position)
        })
    }

    pub(in super::super::super) fn clone_variables(&self) -> Vec<vir_low::VariableDecl> {
        let mut variables = self.variables.clone();
        variables.extend(self.permission_variables.clone());
        variables.extend(self.permission_map_variables.clone());
        variables
    }
}

impl GlobalHeapState {
    pub(super) fn insert(
        &mut self,
        label: String,
        snapshots: &BlockHeap,
    ) -> SpannedEncodingResult<()> {
        let predicate_snapshots = HeapAtLabel {
            owned: snapshots.owned.clone(),
            memory_block: snapshots.memory_block.clone(),
        };
        assert!(self
            .snapshots_at_label
            .insert(label, predicate_snapshots)
            .is_none());
        Ok(())
    }

    pub(super) fn create_snapshot_variable(
        &mut self,
        predicate_name: &str,
        ty: vir_low::Type,
    ) -> vir_low::VariableDecl {
        self.heap_variables
            .create_snapshot_variable(predicate_name, ty)
    }

    pub(super) fn create_merge_variable(&mut self, ty: vir_low::Type) -> vir_low::VariableDecl {
        self.heap_variables.create_merge_variable(ty)
    }

    /// Note: Permission variables are **NOT** SSA.
    pub(super) fn create_permission_variable(
        &mut self,
        predicate_name: &str,
    ) -> vir_low::VariableDecl {
        self.heap_variables
            .create_permission_variable(predicate_name)
    }

    // pub(super) fn create_permission_map(&mut self, ty: vir_low::Type) -> vir_low::VariableDecl {
    //     let permission_variable_name =
    //         format!("permission_map${}", self.permission_map_variables.len());
    //     let variable = vir_low::VariableDecl::new(permission_variable_name, ty);
    //     self.permission_map_variables.push(variable.clone());
    //     variable
    // }

    pub(in super::super::super) fn initialize_permission_variables(
        &self,
        position: vir_low::Position,
    ) -> impl Iterator<Item = vir_low::Statement> + '_ {
        self.heap_variables
            .initialize_permission_variables(position)
    }

    pub(in super::super::super) fn clone_variables(&self) -> Vec<vir_low::VariableDecl> {
        self.heap_variables.clone_variables()
    }
}
