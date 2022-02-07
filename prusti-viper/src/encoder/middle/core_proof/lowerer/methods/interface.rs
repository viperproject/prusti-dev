use crate::encoder::{errors::SpannedEncodingResult, middle::core_proof::lowerer::Lowerer};
use std::collections::BTreeMap;
use vir_crate::low::{self as vir_low};

#[derive(Default)]
pub(in super::super) struct MethodsLowererState {
    methods: BTreeMap<String, vir_low::MethodDecl>,
}

impl MethodsLowererState {
    pub fn destruct(self) -> Vec<vir_low::MethodDecl> {
        self.methods.into_values().collect()
    }
}

pub(in super::super::super) trait MethodsLowererInterface {
    fn declare_method(&mut self, method: vir_low::MethodDecl) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> MethodsLowererInterface for Lowerer<'p, 'v, 'tcx> {
    fn declare_method(&mut self, method: vir_low::MethodDecl) -> SpannedEncodingResult<()> {
        assert!(
            !self.methods_state.methods.contains_key(&method.name),
            "method {} already declared",
            method.name
        );
        self.methods_state
            .methods
            .insert(method.name.clone(), method);
        Ok(())
    }
}
