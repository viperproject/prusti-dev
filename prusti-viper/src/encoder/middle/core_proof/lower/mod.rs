use crate::encoder::Encoder;
use vir_crate::{low as vir_low, middle as vir_mid};

use super::MidCoreProofEncoderInterface;

mod cfg;
mod places;
mod snapshots;

pub(super) trait State {
    fn lower_expression(
        &mut self,
        expression: vir_mid::Expression,
    ) -> vir_low::ast::expression::Expression;
    fn extract_root_address(
        &mut self,
        expression: &vir_mid::Expression,
    ) -> vir_low::ast::expression::Expression;
    fn lower_expression_into_place(
        &mut self,
        expression: &vir_mid::Expression,
    ) -> vir_low::ast::expression::Expression;
    fn lower_expression_into_place_address_computation(
        &mut self,
        expression: &vir_mid::Expression,
    ) -> vir_low::ast::expression::Expression;
    fn lower_expression_into_snapshot(
        &mut self,
        expression: &vir_mid::Expression,
    ) -> vir_low::ast::expression::Expression;
    fn lower_type(&mut self, ty: vir_mid::Type) -> vir_low::ast::ty::Type;
}

pub(super) trait IntoLow<Target> {
    fn into_low(self, state: &mut dyn State) -> Target;
}

impl<'v, 'tcx: 'v> State for Encoder<'v, 'tcx> {
    fn lower_expression(
        &mut self,
        expression: vir_mid::Expression,
    ) -> vir_low::ast::expression::Expression {
        self.lower_expression_into_low(expression)
    }
    fn extract_root_address(
        &mut self,
        place: &vir_mid::Expression,
    ) -> vir_low::ast::expression::Expression {
        assert!(place.is_place());
        self::places::extract_root_address(place)
    }
    fn lower_expression_into_place(
        &mut self,
        place: &vir_mid::Expression,
    ) -> vir_low::ast::expression::Expression {
        assert!(place.is_place());
        self::places::encode_expression_as_place(place)
    }
    fn lower_expression_into_place_address_computation(
        &mut self,
        place: &vir_mid::Expression,
    ) -> vir_low::ast::expression::Expression {
        assert!(place.is_place());
        self::places::compute_stack_place_address(place)
    }
    fn lower_expression_into_snapshot(
        &mut self,
        expression: &vir_mid::Expression,
    ) -> vir_low::ast::expression::Expression {
        self::snapshots::encode_into_snapshot(self, expression)
    }
    fn lower_type(&mut self, ty: vir_mid::Type) -> vir_low::ast::ty::Type {
        self.lower_type_into_low(ty)
    }
}
