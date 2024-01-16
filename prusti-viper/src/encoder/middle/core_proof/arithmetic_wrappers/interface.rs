use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::lowerer::{DomainsLowererInterface, Lowerer},
};
use prusti_common::config;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, QuantifierHelpers},
    low::{self as vir_low},
};

const DOMAIN_NAME: &str = "ArithmeticWrappers";
const ADD_FUNC_NAME: &str = "add_wrapper$";
const MUL_FUNC_NAME: &str = "mul_wrapper$";

pub(in super::super) trait ArithmeticWrappersInterface {
    fn int_add_call(
        &mut self,
        left: vir_low::Expression,
        right: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn int_mul_call(
        &mut self,
        left: vir_low::Expression,
        right: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> ArithmeticWrappersInterface for Lowerer<'p, 'v, 'tcx> {
    fn int_add_call(
        &mut self,
        left: vir_low::Expression,
        right: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if !self.arithmetic_wrapper_state.is_add_encoded {
            self.arithmetic_wrapper_state.is_add_encoded = true;
            use vir_low::macros::*;
            var_decls!(left: Int, right: Int);
            let call = self.create_domain_func_app(
                DOMAIN_NAME,
                ADD_FUNC_NAME,
                vec![left.clone().into(), right.clone().into()],
                vir_low::Type::Int,
                Default::default(),
            )?;
            let body = vir_low::Expression::forall(
                vec![left.clone(), right.clone()],
                vec![vir_low::Trigger::new(vec![call.clone()])],
                vir_low::Expression::equals(
                    call,
                    vir_low::Expression::add(left.into(), right.into()),
                ),
            );
            let axiom = vir_low::DomainAxiomDecl::new(None, "add_wrapper$definition", body);
            self.declare_axiom(DOMAIN_NAME, axiom)?;
        }
        self.create_domain_func_app(
            DOMAIN_NAME,
            ADD_FUNC_NAME,
            vec![left, right],
            vir_low::Type::Int,
            position,
        )
    }
    fn int_mul_call(
        &mut self,
        left: vir_low::Expression,
        right: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if !self.arithmetic_wrapper_state.is_mul_encoded {
            self.arithmetic_wrapper_state.is_mul_encoded = true;
            use vir_low::macros::*;
            var_decls!(left: Int, right: Int);
            let call = self.create_domain_func_app(
                DOMAIN_NAME,
                MUL_FUNC_NAME,
                vec![left.clone().into(), right.clone().into()],
                vir_low::Type::Int,
                Default::default(),
            )?;
            {
                let call_commutative = self.create_domain_func_app(
                    DOMAIN_NAME,
                    MUL_FUNC_NAME,
                    vec![right.clone().into(), left.clone().into()],
                    vir_low::Type::Int,
                    Default::default(),
                )?;
                let body = vir_low::Expression::forall(
                    vec![left.clone(), right.clone()],
                    vec![vir_low::Trigger::new(vec![call.clone()])],
                    vir_low::Expression::equals(call.clone(), call_commutative),
                );
                let axiom = vir_low::DomainAxiomDecl::new(None, "mul_wrapper$commutativity", body);
                self.declare_axiom(DOMAIN_NAME, axiom)?;
            }
            {
                var_decls!(value: Int);
                let call_zero_left = self.create_domain_func_app(
                    DOMAIN_NAME,
                    MUL_FUNC_NAME,
                    vec![0.into(), value.clone().into()],
                    vir_low::Type::Int,
                    Default::default(),
                )?;
                let call_zero_right = self.create_domain_func_app(
                    DOMAIN_NAME,
                    MUL_FUNC_NAME,
                    vec![value.clone().into(), 0.into()],
                    vir_low::Type::Int,
                    Default::default(),
                )?;
                let body = vir_low::Expression::forall(
                    vec![value.clone()],
                    vec![
                        vir_low::Trigger::new(vec![call_zero_left.clone()]),
                        vir_low::Trigger::new(vec![call_zero_right.clone()]),
                    ],
                    vir_low::Expression::and(
                        vir_low::Expression::equals(call_zero_left, 0.into()),
                        vir_low::Expression::equals(call_zero_right, 0.into()),
                    ),
                );
                let axiom = vir_low::DomainAxiomDecl::new(None, "mul_wrapper$zero", body);
                self.declare_axiom(DOMAIN_NAME, axiom)?;
            }
            {
                var_decls!(common: Int, a: Int, b: Int);
                let call_first = self.create_domain_func_app(
                    DOMAIN_NAME,
                    MUL_FUNC_NAME,
                    vec![common.clone().into(), a.clone().into()],
                    vir_low::Type::Int,
                    Default::default(),
                )?;
                let call_second = self.create_domain_func_app(
                    DOMAIN_NAME,
                    MUL_FUNC_NAME,
                    vec![common.clone().into(), b.clone().into()],
                    vir_low::Type::Int,
                    Default::default(),
                )?;
                let body = vir_low::Expression::forall(
                    vec![common.clone(), a.clone(), b.clone()],
                    vec![vir_low::Trigger::new(vec![
                        call_first.clone(),
                        call_second.clone(),
                    ])],
                    expr! {
                        ([0.into()] < common) ==> ((a <= b) ==> ([call_first] <= [call_second]))
                    },
                );
                let axiom =
                    vir_low::DomainAxiomDecl::new(None, "mul_wrapper$non_negative_range", body);
                self.declare_axiom(DOMAIN_NAME, axiom)?;
            }
            {
                var_decls!(a: Int, b: Int);
                let call = self.create_domain_func_app(
                    DOMAIN_NAME,
                    MUL_FUNC_NAME,
                    vec![a.clone().into(), b.clone().into()],
                    vir_low::Type::Int,
                    Default::default(),
                )?;
                let body = vir_low::Expression::forall(
                    vec![a.clone(), b.clone()],
                    vec![vir_low::Trigger::new(vec![call.clone()])],
                    expr! {
                        (([0.into()] < a) && ([0.into()] < b)) ==> (([a.into()] < [call.clone()]) && ([b.into()] < [call]))
                    },
                );
                let axiom =
                    vir_low::DomainAxiomDecl::new(None, "mul_wrapper$positive_increases", body);
                self.declare_axiom(DOMAIN_NAME, axiom)?;
            }
            if config::define_multiply_int() {
                let body = vir_low::Expression::forall(
                    vec![left.clone(), right.clone()],
                    vec![vir_low::Trigger::new(vec![call.clone()])],
                    vir_low::Expression::equals(
                        call,
                        vir_low::Expression::multiply(left.clone().into(), right.clone().into()),
                    ),
                );
                let axiom = vir_low::DomainAxiomDecl::new(None, "mul_wrapper$definition", body);
                self.declare_axiom(DOMAIN_NAME, axiom)?;
            }
        }
        self.create_domain_func_app(
            DOMAIN_NAME,
            MUL_FUNC_NAME,
            vec![left, right],
            vir_low::Type::Int,
            position,
        )
    }
}
