use super::{
    super::utils::place_domain_encoder::PlaceExpressionDomainEncoder, encoder::PlaceEncoder,
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::lowerer::{DomainsLowererInterface, Lowerer},
};
use vir_crate::{
    low as vir_low,
    middle::{self as vir_mid},
};

pub(in super::super) trait PlacesInterface {
    fn place_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn encode_field_place(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_place: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn encode_expression_as_place(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> PlacesInterface for Lowerer<'p, 'v, 'tcx> {
    fn place_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type("Place")
    }
    fn encode_field_place(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_place: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        self.encode_field_access_function_app("Place", base_place, base_type, field, position)
    }
    /// Emits code that represents the place.
    fn encode_expression_as_place(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mut encoder = PlaceEncoder {};
        encoder.encode_expression(place, self)
    }
}
