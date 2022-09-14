use crate::encoder::{errors::SpannedEncodingResult, middle::core_proof::lowerer::Lowerer};
use vir_crate::low::{self as vir_low};

const DOMAIN_NAME: &str = "WildcardPermission";
const FUNCTION_NAME: &str = "wildcard_permission";

pub(in super::super) trait PermissionsInterface {
    fn wildcard_permission(&mut self) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> PermissionsInterface for Lowerer<'p, 'v, 'tcx> {
    fn wildcard_permission(&mut self) -> SpannedEncodingResult<vir_low::Expression> {
        // if !self.permissions_state.is_wildcard_function_encoded {
        //     self.permissions_state.is_wildcard_function_encoded = true;
        //     use vir_low::macros::*;
        //     let call = self.create_domain_func_app(
        //         DOMAIN_NAME,
        //         FUNCTION_NAME,
        //         vec![],
        //         vir_low::Type::Perm,
        //         Default::default(),
        //     )?;
        //     let body = expr! {
        //         ([vir_low::Expression::no_permission()] < [call.clone()]) &&
        //         ([call] < [vir_low::Expression::full_permission()])
        //     };
        //     let axiom =
        //         vir_low::DomainAxiomDecl::new(None, format!("{}$definition", FUNCTION_NAME), body);
        //     self.declare_axiom(DOMAIN_NAME, axiom)?;
        // }
        // self.create_domain_func_app(
        //     DOMAIN_NAME,
        //     FUNCTION_NAME,
        //     vec![],
        //     vir_low::Type::Perm,
        //     Default::default(),
        // )
        Ok(vir_low::Expression::wildcard_permission())
    }
}
