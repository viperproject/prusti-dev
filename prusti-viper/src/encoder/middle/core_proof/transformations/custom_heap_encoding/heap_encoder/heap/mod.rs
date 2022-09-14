use super::HeapEncoder;
use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, QuantifierHelpers},
    low::{self as vir_low},
};

impl<'p, 'v: 'p, 'tcx: 'v> HeapEncoder<'p, 'v, 'tcx> {
    fn heap_version_type(&self) -> vir_low::Type {
        vir_low::Type::domain("HeapVersion".to_string())
    }

    pub(super) fn heap_function_name(&self, predicate_name: &str) -> String {
        format!("heap${predicate_name}")
    }

    pub(super) fn heap_call(
        &mut self,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        mut arguments: Vec<vir_low::Expression>,
        heap_version: vir_low::Expression,
    ) -> SpannedEncodingResult<Option<vir_low::Expression>> {
        let call =
            if let Some(snapshot_type) = self.get_snapshot_type_for_predicate(&predicate.name) {
                let heap_function_name = self.heap_function_name(&predicate.name);
                arguments.push(heap_version);
                Some(vir_low::Expression::domain_function_call(
                    "HeapFunctions",
                    heap_function_name,
                    arguments,
                    snapshot_type,
                ))
            } else {
                None
            };
        Ok(call)
    }

    pub(super) fn heap_call_for_predicate_def(
        &mut self,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        heap_version: vir_low::Expression,
    ) -> SpannedEncodingResult<Option<vir_low::Expression>> {
        let arguments = self.get_predicate_parameters_as_arguments(&predicate.name)?;
        self.heap_call(predicate, arguments, heap_version)
    }

    pub(super) fn encode_heap_unchanged_quantifier(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        new_permission_mask: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let heap_version_old = self.get_current_heap_version_for(&predicate.name)?;
        if let Some(heap_old) = self.heap_call_for_predicate_def(predicate, heap_version_old)? {
            let heap_version_new = self.get_new_heap_version_for(&predicate.name, position)?;
            let heap_new = self
                .heap_call_for_predicate_def(predicate, heap_version_new)?
                .unwrap();
            let predicate_parameters = self.get_predicate_parameters(&predicate.name).to_owned();
            let triggers = vec![vir_low::Trigger::new(vec![heap_new.clone()])];
            let guard = self
                .positive_permission_mask_call_for_predicate_def(predicate, new_permission_mask)?;
            let body = vir_low::Expression::implies(
                guard,
                vir_low::Expression::equals(heap_old, heap_new),
            );
            statements.push(vir_low::Statement::assume(
                vir_low::Expression::forall(predicate_parameters, triggers, body),
                position,
            ));
        }
        Ok(())
    }

    pub(super) fn get_current_heap_version_for(
        &mut self,
        predicate_name: &str,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let variable_name = self.heap_names.get(predicate_name).unwrap();
        let version = self.ssa_state.current_variable_version(variable_name);
        let ty = self.heap_version_type();
        Ok(self
            .new_variables
            .create_variable(variable_name, ty, version)?
            .into())
    }

    fn get_new_heap_version_for(
        &mut self,
        predicate_name: &str,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let variable_name = self.heap_names.get(predicate_name).unwrap();
        let ty = self.heap_version_type();
        let version = self
            .ssa_state
            .new_variable_version(variable_name, &ty, position);
        Ok(self
            .new_variables
            .create_variable(variable_name, ty, version)?
            .into())
    }

    pub(super) fn get_heap_version_at_label(
        &mut self,
        predicate_name: &str,
        label: &str,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let variable_name = self.heap_names.get(predicate_name).unwrap();
        let version = self
            .ssa_state
            .variable_version_at_label(variable_name, label);
        let ty = self.heap_version_type();
        Ok(self
            .new_variables
            .create_variable(variable_name, ty, version)?
            .into())
    }

    pub(super) fn generate_heap_domains(
        &self,
        domains: &mut Vec<vir_low::DomainDecl>,
    ) -> SpannedEncodingResult<()> {
        let heap_version_domain =
            vir_low::DomainDecl::new("HeapVersion", Vec::new(), Vec::new(), Vec::new());
        domains.push(heap_version_domain);
        let mut functions = Vec::new();
        for predicate in self.predicates.iter_decls() {
            if let Some(snapshot_type) = self.get_snapshot_type_for_predicate(&predicate.name) {
                let mut parameters = predicate.parameters.clone();
                parameters.push(vir_low::VariableDecl::new(
                    "version",
                    self.heap_version_type(),
                ));
                functions.push(vir_low::DomainFunctionDecl::new(
                    self.heap_function_name(&predicate.name),
                    false,
                    parameters,
                    snapshot_type,
                ));
            }
        }
        let heap_domain =
            vir_low::DomainDecl::new("HeapFunctions", functions, Vec::new(), Vec::new());
        domains.push(heap_domain);
        Ok(())
    }
}
