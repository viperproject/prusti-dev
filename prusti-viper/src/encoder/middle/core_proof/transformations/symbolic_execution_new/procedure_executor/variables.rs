use super::{super::super::encoder_context::EncoderContext, ProcedureExecutor};
use crate::encoder::errors::SpannedEncodingResult;

use std::collections::BTreeMap;
use vir_crate::low::{self as vir_low};

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn create_new_bool_variable_version(
        &mut self,
        variable_name: &str,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let version = self
            .variable_versions
            .versions
            .entry(variable_name.to_string())
            .or_default();
        *version += 1;
        let version = *version;
        let variable =
            vir_low::VariableDecl::new(format!("{variable_name}${version}"), vir_low::Type::Bool);
        Ok(variable)
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct VariableVersions {
    pub(super) versions: BTreeMap<String, usize>,
}

impl VariableVersions {
    pub(super) fn create_variable_decls(&self) -> Vec<vir_low::VariableDecl> {
        let mut variables = Vec::new();
        for (name, last_version) in &self.versions {
            for version in 0..=*last_version {
                variables.push(vir_low::VariableDecl::new(
                    format!("{name}${version}"),
                    vir_low::Type::Bool,
                ));
            }
        }
        variables
    }
}
