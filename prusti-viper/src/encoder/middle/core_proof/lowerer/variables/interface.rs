use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{into_low::IntoLow, lowerer::Lowerer},
};
use std::collections::BTreeMap;
use vir_crate::{
    low::{self as vir_low},
    middle as vir_mid,
};

#[derive(Default)]
pub(in super::super) struct VariablesLowererState {
    variables: BTreeMap<String, vir_low::Type>,
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
    fn collect_existing_variables(
        &mut self,
        procedure: &vir_mid::ProcedureDecl,
    ) -> SpannedEncodingResult<()>;
    fn create_variable(
        &mut self,
        name: String,
        ty: vir_low::Type,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
}

impl<'p, 'v: 'p, 'tcx: 'v> VariablesLowererInterface for Lowerer<'p, 'v, 'tcx> {
    fn collect_existing_variables(
        &mut self,
        procedure: &vir_mid::ProcedureDecl,
    ) -> SpannedEncodingResult<()> {
        assert!(
            self.variables_state.variables.is_empty(),
            "This method should be called before any variables are created"
        );
        self.variables_state.variables = procedure
            .collect_locals()
            .into_low(self)?
            .into_iter()
            .map(|variable| (variable.name, variable.ty))
            .collect();
        Ok(())
    }
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
}
