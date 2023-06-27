use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::lowerer::{DomainsLowererInterface, Lowerer},
};
use vir_crate::{
    common::{expression::QuantifierHelpers, identifier::WithIdentifier},
    low::{self as vir_low, operations::ty::Typed},
};

const DOMAIN_NAME: &str = "Triggers";

pub(in super::super) trait TriggersInterface {
    fn trigger_expression(
        &mut self,
        expression: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn call_trigger_function(
        &mut self,
        function_name: &str,
        arguments: Vec<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> TriggersInterface for Lowerer<'p, 'v, 'tcx> {
    fn trigger_expression(
        &mut self,
        expression: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let identifier = expression.get_type().get_identifier();
        let function_name = format!("trigger${}", identifier);
        if !self
            .triggers_state
            .encoded_triggering_functions
            .contains(&identifier)
        {
            self.triggers_state
                .encoded_triggering_functions
                .insert(identifier);
            use vir_low::macros::*;
            var_decls!(value: {expression.get_type().clone()});
            let call = self.create_domain_func_app(
                DOMAIN_NAME,
                function_name.clone(),
                vec![value.clone().into()],
                vir_low::Type::Bool,
                Default::default(),
            )?;
            let body = vir_low::Expression::forall(
                vec![value],
                vec![vir_low::Trigger::new(vec![call.clone()])],
                call,
            );
            let axiom =
                vir_low::DomainAxiomDecl::new(None, format!("{}$definition", function_name), body);
            self.declare_axiom(DOMAIN_NAME, axiom)?;
        }
        self.create_domain_func_app(
            DOMAIN_NAME,
            function_name,
            vec![expression],
            vir_low::Type::Bool,
            position,
        )
    }

    fn call_trigger_function(
        &mut self,
        function_name: &str,
        arguments: Vec<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if !self
            .triggers_state
            .encoded_triggering_functions
            .contains(function_name)
        {
            self.triggers_state
                .encoded_triggering_functions
                .insert(function_name.to_string());
            let mut variables = Vec::new();
            for (i, argument) in arguments.iter().enumerate() {
                variables.push(vir_low::VariableDecl::new(
                    format!("_{}", i),
                    argument.get_type().clone(),
                ));
            }
            let call = self.create_domain_func_app(
                DOMAIN_NAME,
                function_name,
                variables.iter().map(|v| v.clone().into()).collect(),
                vir_low::Type::Bool,
                Default::default(),
            )?;
            let body = vir_low::Expression::forall(
                variables,
                vec![vir_low::Trigger::new(vec![call.clone()])],
                call,
            );
            let axiom =
                vir_low::DomainAxiomDecl::new(None, format!("{}$definition", function_name), body);
            self.declare_axiom(DOMAIN_NAME, axiom)?;
        }
        self.create_domain_func_app(
            DOMAIN_NAME,
            function_name,
            arguments,
            vir_low::Type::Bool,
            position,
        )
    }
}
