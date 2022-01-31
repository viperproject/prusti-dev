use super::{
    super::utils::place_domain_encoder::PlaceExpressionDomainEncoder, encoder::PlaceAddressEncoder,
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::lowerer::{DomainsLowererInterface, Lowerer, VariablesLowererInterface},
};
use vir_crate::{
    low as vir_low,
    middle::{self as vir_mid},
};

pub(in super::super) trait AddressesInterface {
    fn address_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    /// Constructs a variable representing the address of the given MIR-level
    /// variable.
    fn root_address(
        &mut self,
        local: &vir_mid::expression::Local,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    /// Get the variable representing the root address of this place.
    fn extract_root_address(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_field_address(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_address: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn encode_expression_as_place_address(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> AddressesInterface for Lowerer<'p, 'v, 'tcx> {
    fn address_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type("Address")
    }
    fn root_address(
        &mut self,
        local: &vir_mid::expression::Local,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let name = format!("{}$address", local.variable.name);
        let ty = self.address_type()?;
        let address_variable = self.create_variable(name, ty)?;
        Ok(vir_low::Expression::local(address_variable, local.position))
    }
    fn extract_root_address(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(place.is_place());
        let result = match place {
            vir_mid::Expression::Local(local) => self.root_address(local)?,
            vir_mid::Expression::LabelledOld(_) => unimplemented!(),
            _ => self.extract_root_address(place.get_parent_ref().unwrap())?,
        };
        Ok(result)
    }
    fn encode_field_address(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_address: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        self.encode_field_access_function_app("Address", base_address, base_type, field, position)
    }
    /// Emits code that represents the place's address.
    fn encode_expression_as_place_address(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mut encoder = PlaceAddressEncoder {};
        encoder.encode_expression(place, self)
    }
}
