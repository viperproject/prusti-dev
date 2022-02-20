use vir_crate::{
    common::expression::{ExpressionIterator, QuantifierHelpers},
    low::{self as vir_low},
};

pub(super) const CONSTANT_VARIANT: &str = "constant$";
pub(super) const CONSTANT_FIELD: &str = "constant";
pub(super) const BASE_VARIANT: &str = "base$";

pub(in super::super) struct AdtConstructor {
    variant: String,
    parameters: Vec<vir_low::VariableDecl>,
}

impl AdtConstructor {
    pub(in super::super) fn constant(parameter_type: vir_crate::low::Type) -> AdtConstructor {
        Self {
            variant: CONSTANT_VARIANT.to_string(),
            parameters: vec![vir_low::VariableDecl::new(CONSTANT_FIELD, parameter_type)],
        }
    }

    pub(in super::super) fn variant(
        variant: String,
        parameters: Vec<vir_low::VariableDecl>,
    ) -> AdtConstructor {
        Self {
            variant,
            parameters,
        }
    }

    pub(in super::super) fn base(parameters: Vec<vir_low::VariableDecl>) -> AdtConstructor {
        Self {
            variant: "base$".to_string(),
            parameters,
        }
    }

    pub(in super::super) fn get_variant(&self) -> &str {
        &self.variant
    }

    pub(in super::super) fn get_parameters(&self) -> &[vir_low::VariableDecl] {
        &self.parameters
    }

    fn destructor_name(&self, domain_name: &str, field_name: &str) -> String {
        destructor_name(domain_name, &self.variant, field_name)
    }

    pub(in super::super) fn create_constructor_function(
        &self,
        domain_name: &str,
    ) -> vir_low::DomainFunctionDecl {
        vir_low::DomainFunctionDecl {
            name: constructor_name(domain_name, &self.variant),
            parameters: self.parameters.clone(),
            return_type: constructor_return_type(domain_name),
        }
    }

    pub(in super::super) fn constructor_call(
        &self,
        domain_name: &str,
        arguments: Vec<vir_low::Expression>,
    ) -> vir_low::Expression {
        constructor_call(domain_name, &self.variant, arguments)
    }

    pub(in super::super) fn default_constructor_call(
        &self,
        domain_name: &str,
    ) -> vir_low::Expression {
        self.constructor_call(
            domain_name,
            self.parameters
                .iter()
                .map(|argument| argument.clone().into())
                .collect(),
        )
    }

    pub(in super::super) fn constructor_name(&self, domain_name: &str) -> String {
        constructor_name(domain_name, &self.variant)
    }

    pub(in super::super) fn create_destructor_functions(
        &self,
        domain_name: &str,
    ) -> Vec<vir_low::DomainFunctionDecl> {
        let parameter =
            vir_low::VariableDecl::new("value", vir_low::Type::domain(domain_name.to_string()));
        self.parameters
            .iter()
            .map(|field| vir_low::DomainFunctionDecl {
                name: self.destructor_name(domain_name, &field.name),
                parameters: vec![parameter.clone()],
                return_type: field.ty.clone(),
            })
            .collect()
    }

    pub(in super::super) fn create_injectivity_axioms(
        &self,
        domain_name: &str,
    ) -> Vec<vir_low::DomainAxiomDecl> {
        let constructor_call = self.default_constructor_call(domain_name);
        let axioms = if self.parameters.is_empty() {
            vec![]
        } else {
            use vir_low::macros::*;
            let mut triggers = Vec::new();
            let mut conjuncts = Vec::new();
            for field in &self.parameters {
                let destructor_call = destructor_call(
                    domain_name,
                    &self.variant,
                    &field.name,
                    field.ty.clone(),
                    constructor_call.clone(),
                );
                triggers.push(vir_low::Trigger::new(vec![destructor_call.clone()]));
                conjuncts.push(expr! { [destructor_call] == field });
            }
            let body = vir_low::Expression::forall(
                self.parameters.clone(),
                triggers,
                conjuncts.into_iter().conjoin(),
            );
            vec![vir_low::DomainAxiomDecl {
                name: format!(
                    "{}$injectivity_axiom",
                    constructor_name(domain_name, &self.variant)
                ),
                body,
            }]
        };
        axioms
    }
}

pub(super) fn constructor_call(
    domain_name: &str,
    variant: &str,
    arguments: Vec<vir_low::Expression>,
) -> vir_low::Expression {
    vir_low::Expression::domain_function_call(
        domain_name.to_string(),
        constructor_name(domain_name, variant),
        arguments,
        constructor_return_type(domain_name),
    )
}

pub(super) fn destructor_call(
    domain_name: &str,
    variant: &str,
    field_name: &str,
    field_type: vir_low::Type,
    argument: vir_low::Expression,
) -> vir_low::Expression {
    vir_low::Expression::domain_function_call(
        domain_name.to_string(),
        destructor_name(domain_name, variant, field_name),
        vec![argument],
        field_type,
    )
}

fn constructor_return_type(domain_name: &str) -> vir_low::Type {
    vir_low::Type::domain(domain_name.to_string())
}

pub(super) fn constructor_name(domain_name: &str, variant: &str) -> String {
    format!("constructor${}${}", domain_name, variant)
}

pub(super) fn destructor_name(domain_name: &str, variant: &str, field_name: &str) -> String {
    format!("field${}${}${}", domain_name, variant, field_name)
}
