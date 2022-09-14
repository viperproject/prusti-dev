use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::lowerer::{DomainsLowererInterface, Lowerer},
};
use vir_crate::{
    common::expression::{BinaryOperationHelpers, QuantifierHelpers},
    low::{self as vir_low},
};

const DOMAIN_NAME: &str = "ArithmeticWrappers";
const ADD_FUNC_NAME: &str = "add_wrapper$";

pub(in super::super) trait ArithmeticWrappersInterface {
    fn int_add_call(
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
}
