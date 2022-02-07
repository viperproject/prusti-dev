use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{lowerer::Lowerer, snapshots::IntoSnapshot},
};

use vir_crate::{low as vir_low, middle as vir_mid};

pub(in super::super) trait IntoLowInterface {
    fn lower_expression(
        &mut self,
        expression: vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn lower_expression_into_snapshot(
        &mut self,
        expression: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn lower_type(&mut self, ty: vir_mid::Type) -> SpannedEncodingResult<vir_low::ast::ty::Type>;
}

impl<'p, 'v: 'p, 'tcx: 'v> IntoLowInterface for Lowerer<'p, 'v, 'tcx> {
    fn lower_expression(
        &mut self,
        expression: vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        vir_low::operations::ToLowLowerer::to_low_expression(self, expression)
    }
    fn lower_expression_into_snapshot(
        &mut self,
        expression: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        expression.create_snapshot(self)
    }
    fn lower_type(&mut self, ty: vir_mid::Type) -> SpannedEncodingResult<vir_low::ast::ty::Type> {
        vir_low::operations::ToLowLowerer::to_low_type(self, ty)
    }
}
