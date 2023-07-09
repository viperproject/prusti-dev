use super::HeapEncoder;
use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use rustc_hash::FxHashSet;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, ExpressionIterator, QuantifierHelpers},
    low::{
        self as vir_low,
        expression::visitors::{ExpressionFallibleFolder, ExpressionFolder},
    },
};

impl<'p, 'v: 'p, 'tcx: 'v> HeapEncoder<'p, 'v, 'tcx> {
    fn heap_version_type(&self) -> vir_low::Type {
        vir_low::Type::domain("HeapVersion".to_string())
    }

    pub(super) fn heap_function_name(&self, predicate_name: &str) -> String {
        format!("heap${predicate_name}")
    }

    pub(super) fn heap_range_function_name(&self, predicate_name: &str) -> String {
        format!("heap_range${predicate_name}")
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
        let mut axioms = Vec::new();
        let mut already_encoded_ensures_validity_functions = FxHashSet::default();
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
                    snapshot_type.clone(),
                ));
                if predicate.kind == vir_low::PredicateKind::Owned
                    && !already_encoded_ensures_validity_functions.contains(&snapshot_type)
                {
                    already_encoded_ensures_validity_functions.insert(snapshot_type.clone());
                    // Ensures validity function definition.
                    let vir_low::Type::Domain(snapshot_domain) = &snapshot_type else {
                        unreachable!("snapshot_type: {snapshot_type}")
                    };
                    // FIXME: Do not rely on strings. Use OwnedPredicateInfo instead.
                    let validity_function_name = format!("valid${}", snapshot_domain.name);
                    let ensures_validity_function_name =
                        format!("ensures${}", validity_function_name);
                    let parameter = vir_low::VariableDecl::new("snapshot", snapshot_type.clone());
                    functions.push(vir_low::DomainFunctionDecl::new(
                        ensures_validity_function_name.clone(),
                        false,
                        vec![parameter.clone()],
                        snapshot_type.clone(),
                    ));
                    let function_call = vir_low::Expression::domain_function_call(
                        "HeapFunctions",
                        ensures_validity_function_name.clone(),
                        vec![parameter.clone().into()],
                        snapshot_type.clone(),
                    );
                    let validity_function_call = vir_low::Expression::domain_function_call(
                        snapshot_domain.name.clone(),
                        validity_function_name.clone(),
                        vec![parameter.clone().into()],
                        vir_low::Type::Bool,
                    );
                    let axiom_body = vir_low::Expression::forall(
                        vec![parameter.clone()],
                        vec![vir_low::Trigger::new(vec![function_call.clone()])],
                        vir_low::Expression::and(
                            vir_low::Expression::equals(function_call, parameter.clone().into()),
                            validity_function_call,
                        ),
                    );
                    let definitional_axiom = vir_low::DomainAxiomDecl::new(
                        None,
                        format!("{}$definitional_axiom", ensures_validity_function_name),
                        axiom_body,
                    );
                    axioms.push(definitional_axiom);
                }
            }
        }
        for (range_function_name, predicate) in self.predicates.iter_range_functions() {
            if let Some(snapshot_type) = self.get_snapshot_type_for_predicate(&predicate.name) {
                if let Some(function_decl) = self.functions.get(range_function_name) {
                    eprintln!("range_function_name: {}", range_function_name);
                    eprintln!("predicate: {}", predicate);
                    eprintln!("snapshot_type: {}", snapshot_type);
                    eprintln!("function_decl: {}", function_decl);
                    let function_name = self.heap_range_function_name(&predicate.name);
                    eprintln!("function_name: {}", function_name);
                    let mut parameters = function_decl.parameters.clone();
                    let heap_version =
                        vir_low::VariableDecl::new("version", self.heap_version_type());
                    parameters.push(heap_version.clone());
                    functions.push(vir_low::DomainFunctionDecl::new(
                        function_name.clone(),
                        false,
                        parameters.clone(),
                        function_decl.return_type.clone(),
                    ));
                    let arguments = parameters
                        .iter()
                        .map(|parameter| parameter.clone().into())
                        .collect();
                    let function_call = vir_low::Expression::domain_function_call(
                        "HeapFunctions",
                        function_name.clone(),
                        arguments,
                        function_decl.return_type.clone(),
                    );
                    struct Rewriter<'a, 'p, 'v, 'tcx> {
                        function_call: &'a vir_low::Expression,
                        heap_encoder: &'a HeapEncoder<'p, 'v, 'tcx>,
                        heap_version: &'a vir_low::VariableDecl,
                    }
                    impl<'a, 'p, 'v, 'tcx> ExpressionFallibleFolder for Rewriter<'a, 'p, 'v, 'tcx> {
                        type Error = SpannedEncodingError;
                        fn fallible_fold_local_enum(
                            &mut self,
                            local: vir_low::Local,
                        ) -> SpannedEncodingResult<vir_low::Expression> {
                            let local = if local.variable.is_result_variable() {
                                self.function_call.clone()
                            } else {
                                vir_low::Expression::Local(local)
                            };
                            Ok(local)
                        }
                        fn fallible_fold_func_app_enum(
                            &mut self,
                            func_app: vir_low::FuncApp,
                        ) -> SpannedEncodingResult<vir_low::Expression> {
                            let func_app = self.fallible_fold_func_app(func_app)?;
                            let function = self.heap_encoder.functions[&func_app.function_name];
                            match function.kind {
                                vir_low::FunctionKind::Snap => {
                                    let predicate_name = self
                                        .heap_encoder
                                        .get_predicate_name_for_function(&func_app.function_name)?;
                                    let mut arguments = func_app.arguments;
                                    arguments.push(self.heap_version.clone().into());
                                    let heap_function_name =
                                        self.heap_encoder.heap_function_name(&predicate_name);
                                    Ok(vir_low::Expression::domain_function_call(
                                        "HeapFunctions",
                                        heap_function_name,
                                        arguments,
                                        func_app.return_type,
                                    ))
                                }
                                _ => unreachable!("unexpected kind: {}", function.kind),
                            }
                        }
                        fn fallible_fold_trigger(
                            &mut self,
                            mut trigger: vir_low::Trigger,
                        ) -> SpannedEncodingResult<vir_low::Trigger> {
                            for term in std::mem::take(&mut trigger.terms) {
                                let term = self.fallible_fold_expression(term)?;
                                trigger.terms.push(term);
                            }
                            Ok(trigger)
                        }
                    }
                    let mut rewriter = Rewriter {
                        function_call: &function_call,
                        heap_encoder: self,
                        heap_version: &heap_version,
                    };
                    let mut conjuncts = Vec::new();
                    for postcondition in &function_decl.posts {
                        let postcondition =
                            rewriter.fallible_fold_expression(postcondition.clone())?;
                        conjuncts.push(postcondition);
                    }
                    let axiom_body = vir_low::Expression::forall(
                        parameters,
                        vec![vir_low::Trigger::new(vec![function_call])],
                        conjuncts.into_iter().conjoin(),
                    );
                    let definitional_axiom = vir_low::DomainAxiomDecl::new(
                        None,
                        format!("{}$definitional_axiom", function_name),
                        axiom_body,
                    );
                    axioms.push(definitional_axiom);
                }
            }
        }
        let heap_domain = vir_low::DomainDecl::new("HeapFunctions", functions, axioms, Vec::new());
        domains.push(heap_domain);
        Ok(())
    }
}
