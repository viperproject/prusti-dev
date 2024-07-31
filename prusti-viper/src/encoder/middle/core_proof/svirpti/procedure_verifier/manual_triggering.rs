//! Ensure that certain axioms are triggered even if the triggering term is
//! originally under a conditional. This property is ensured by pulling the
//! triggering terms to the top level.

use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        svirpti::smt::{Info, SmtSolver, Sort2SmtWrap},
        transformations::{
            encoder_context::EncoderContext, symbolic_execution_new::ProgramContext,
        },
    },
};
use rustc_hash::FxHashMap;
use vir_crate::{
    common::expression::UnaryOperationHelpers,
    low::{self as vir_low, expression::visitors::ExpressionWalker},
};

#[derive(Default)]
pub(super) struct TriggerWrappers {
    emitted_bool_wrapper: bool,
}
impl TriggerWrappers {
    pub(super) fn emit_wrappers(&self, smt_solver: &mut SmtSolver) -> SpannedEncodingResult<()> {
        smt_solver
            .declare_function(
                "Wrappers",
                "wrap_bool_call",
                &vec![vir_low::Type::Bool.wrap()],
                &vir_low::Type::Bool.wrap(),
            )
            .unwrap(); // TODO: handle error
        Ok(())
    }
}

pub(super) struct TriggerTermCollector<'a, 'c, EC: EncoderContext> {
    terms: Vec<(&'static str, vir_low::Expression)>,
    need_bool_wrapper: bool,
    program_context: &'a ProgramContext<'c, EC>,
    address_range_contains_definitional_axiom: &'a vir_low::DomainAxiomDecl,
    disable_offset_address: bool,
    offset_address_definitional_axiom: &'a vir_low::DomainAxiomDecl,
    address_constructor_injectivity_axiom2: &'a vir_low::DomainAxiomDecl,
    usize_validity_bottom_up_axiom: &'a vir_low::DomainAxiomDecl,
}

impl<'a, 'c, EC: EncoderContext> TriggerTermCollector<'a, 'c, EC> {
    pub(super) fn new(program_context: &'a ProgramContext<'c, EC>) -> Self {
        let domains = program_context.get_domains();
        let address_domain = domains
            .iter()
            .find(|domain| domain.name == "Address")
            .unwrap();
        let address_range_contains_definitional_axiom = address_domain
            .axioms
            .iter()
            .find(|axiom| axiom.name == "address_range_contains$definition")
            .unwrap();
        let offset_address_definitional_axiom = address_domain
            .axioms
            .iter()
            .find(|axiom| axiom.name == "offset_address$definition")
            .unwrap();
        let address_constructor_injectivity_axiom2 = address_domain
            .axioms
            .iter()
            .find(|axiom| axiom.name == "address_constructor$injectivity2")
            .unwrap();
        let snap_usize_domain = domains
            .iter()
            .find(|domain| domain.name == "Snap$Usize")
            .unwrap();
        let usize_validity_bottom_up_axiom = snap_usize_domain
            .axioms
            .iter()
            .find(|axiom| axiom.name == "Snap$Usize$$validity_axiom_bottom_up_alternative")
            .unwrap();
        Self {
            terms: Vec::new(),
            need_bool_wrapper: false,
            program_context,
            address_range_contains_definitional_axiom,
            disable_offset_address: false,
            offset_address_definitional_axiom,
            address_constructor_injectivity_axiom2,
            usize_validity_bottom_up_axiom,
        }
    }

    pub(super) fn analyse_expression(&mut self, expression: &vir_low::Expression) {
        self.walk_expression(expression);
    }

    pub(super) fn emit_triggering_terms(
        &self,
        smt_solver: &mut SmtSolver,
        trigger_wrappers: &mut TriggerWrappers,
    ) -> SpannedEncodingResult<()> {
        let info = Info {
            program_context: self.program_context,
        };
        // if self.need_bool_wrapper && !trigger_wrappers.emitted_bool_wrapper {
        //     // trigger_wrappers.emitted_bool_wrapper = true;
        //     smt_solver
        //         .declare_function(
        //             "Wrappers",
        //             "wrap_bool_call",
        //             &vec![vir_low::Type::Bool.wrap()],
        //             &vir_low::Type::Bool.wrap(),
        //         )
        //         .unwrap(); // TODO: handle error
        // }
        for (comment, term) in &self.terms {
            smt_solver.comment(comment).unwrap();
            smt_solver.assert(term, info).unwrap() // TODO: handle error
        }
        Ok(())
    }
}

impl<'a, 'c, EC: EncoderContext> ExpressionWalker for TriggerTermCollector<'a, 'c, EC> {
    fn walk_domain_func_app_enum(&mut self, domain_func_app: &vir_low::DomainFuncApp) {
        if domain_func_app.domain_name == "Address" {
            if domain_func_app.function_name == "address_range_contains$" {
                // self.need_bool_wrapper = true;
                // let wrapper = vir_low::Expression::domain_function_call(
                //     "Wrappers",
                //     "wrap_bool_call",
                //     vec![vir_low::Expression::DomainFuncApp(domain_func_app.clone())],
                //     vir_low::Type::Bool,
                // );
                // self.terms.push(wrapper);

                let axiom_body = &self.address_range_contains_definitional_axiom.body;
                let vir_low::Expression::Quantifier(quantifier) = axiom_body else {
                    unreachable!()
                };
                let replacements = quantifier
                    .variables
                    .iter()
                    .zip(domain_func_app.arguments.iter())
                    .collect();
                let term = quantifier.body.clone().substitute_variables(&replacements);
                self.terms.push((
                    "Manually triggering: address_range_contains$definition",
                    term,
                ));
            } else if domain_func_app.function_name == "offset_address$"
                && !self.disable_offset_address
            {
                let axiom_body = &self.offset_address_definitional_axiom.body;
                let vir_low::Expression::Quantifier(quantifier) = axiom_body else {
                    unreachable!()
                };
                let replacements = quantifier
                    .variables
                    .iter()
                    .zip(domain_func_app.arguments.iter())
                    .collect();
                let term = quantifier.body.clone().substitute_variables(&replacements);
                self.disable_offset_address = true;
                self.walk_expression(&term);
                self.disable_offset_address = false;
                self.terms
                    .push(("Manually triggering: offset_address$definition", term));
            } else if domain_func_app.function_name == "address_constructor$" {
                match &domain_func_app.arguments[0] {
                    vir_low::Expression::DomainFuncApp(vir_low::DomainFuncApp {
                        domain_name,
                        function_name,
                        arguments,
                        ..
                    }) if domain_name == "Address" && function_name == "get_allocation$" => {
                        let axiom_body = &self.address_constructor_injectivity_axiom2.body;
                        let vir_low::Expression::Quantifier(quantifier) = axiom_body else {
                            unreachable!()
                        };
                        assert_eq!(arguments.len(), 1);
                        assert_eq!(quantifier.variables.len(), 3);
                        let address = &arguments[0];
                        let mut replacements = FxHashMap::default();
                        replacements.insert(&quantifier.variables[0], address);
                        replacements
                            .insert(&quantifier.variables[1], &domain_func_app.arguments[1]);
                        replacements
                            .insert(&quantifier.variables[2], &domain_func_app.arguments[2]);
                        let term = quantifier.body.clone().substitute_variables(&replacements);
                        self.terms.push((
                            "Manually triggering: address_constructor$injectivity2",
                            term,
                        ));
                    }
                    _ => {}
                }
            }
        } else if domain_func_app.domain_name == "Snap$Usize" {
            if domain_func_app.function_name == "constructor$Snap$Usize$" {
                assert_eq!(domain_func_app.arguments.len(), 1);
                if matches!(
                    domain_func_app.arguments[0],
                    vir_low::Expression::Constant(_)
                ) {
                    let axiom_body = &self.usize_validity_bottom_up_axiom.body;
                    let vir_low::Expression::Quantifier(quantifier) = axiom_body else {
                        unreachable!()
                    };
                    assert_eq!(quantifier.variables.len(), 1);
                    let replacements = quantifier
                        .variables
                        .iter()
                        .zip(domain_func_app.arguments.iter())
                        .collect();
                    let term = quantifier.body.clone().substitute_variables(&replacements);
                    self.terms.push((
                        "Manually triggering: Snap$Usize$$validity_axiom_bottom_up_alternative",
                        term,
                    ));
                }
            }
        }
        self.walk_domain_func_app(domain_func_app)
    }
}
