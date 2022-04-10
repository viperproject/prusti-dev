use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::Lowerer,
        snapshots::{IntoSnapshot, SnapshotValuesInterface},
    },
};

use vir_crate::{
    common::position::Positioned,
    low as vir_low,
    middle::{self as vir_mid, operations::ty::Typed},
};

pub(in super::super) trait IntoLowInterface {
    fn lower_expression(
        &mut self,
        expression: vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn lower_expression_into_snapshot(
        &mut self,
        expression: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn lower_expression_into_snapshot_constant_value(
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
    fn lower_expression_into_snapshot_constant_value(
        &mut self,
        expression: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        let snapshot = self.lower_expression_into_snapshot(expression)?;
        self.obtain_constant_value(expression.get_type(), snapshot, expression.position())
    }
    fn lower_type(&mut self, ty: vir_mid::Type) -> SpannedEncodingResult<vir_low::ast::ty::Type> {
        vir_low::operations::ToLowLowerer::to_low_type(self, ty)
    }
}
