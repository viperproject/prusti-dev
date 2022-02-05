use crate::encoder::{errors::SpannedEncodingResult, middle::core_proof::lowerer::Lowerer};
use std::collections::BTreeMap;
use vir_crate::low::{self as vir_low};

#[derive(Default)]
pub(in super::super) struct VariablesLowererState {
    variables: BTreeMap<String, vir_low::Type>,
    /// A counter for creating fresh temporary variables.
    tmp_counter: u64,
}

impl VariablesLowererState {
    pub fn destruct(self) -> Vec<vir_low::VariableDecl> {
        self.variables
            .into_iter()
            .map(|(name, ty)| vir_low::VariableDecl::new(name, ty))
            .collect()
    }
}

pub(in super::super::super) trait VariablesLowererInterface {
    fn create_variable(
        &mut self,
        name: String,
        ty: vir_low::Type,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn create_new_temporary_variable(
        &mut self,
        ty: vir_low::Type,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
}

impl<'p, 'v: 'p, 'tcx: 'v> VariablesLowererInterface for Lowerer<'p, 'v, 'tcx> {
    fn create_variable(
        &mut self,
        name: String,
        ty: vir_low::Type,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        if !self.variables_state.variables.contains_key(&name) {
            self.variables_state
                .variables
                .insert(name.clone(), ty.clone());
        }
        Ok(vir_low::VariableDecl::new(name, ty))
    }
    fn create_new_temporary_variable(
        &mut self,
        ty: vir_low::Type,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let name = format!("tmp${}", self.variables_state.tmp_counter);
        self.variables_state.tmp_counter += 1;
        self.create_variable(name, ty)
    }
}
