use crate::encoder::errors::SpannedEncodingResult;
use rustc_hash::FxHashSet;

use vir_crate::low::{self as vir_low};

#[derive(Default)]
pub(super) struct VariableDeclarations {
    variables: FxHashSet<vir_low::VariableDecl>,
    fresh_variable_counter: u64,
}

impl VariableDeclarations {
    pub(super) fn create_variable(
        &mut self,
        variable_name: &str,
        ty: vir_low::Type,
        version: u64,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let variable = vir_low::VariableDecl::new(format!("{variable_name}_{version}"), ty);
        self.variables.insert(variable.clone());
        Ok(variable)
    }

    pub(super) fn fresh_variable(
        &mut self,
        variable_name: &str,
        ty: &vir_low::Type,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let count = self.fresh_variable_counter;
        self.fresh_variable_counter += 1;
        let variable =
            vir_low::VariableDecl::new(format!("{variable_name}$fresh${count}"), ty.clone());
        self.variables.insert(variable.clone());
        Ok(variable)
    }

    pub(super) fn take_variables(&mut self) -> FxHashSet<vir_low::VariableDecl> {
        std::mem::take(&mut self.variables)
    }
}
