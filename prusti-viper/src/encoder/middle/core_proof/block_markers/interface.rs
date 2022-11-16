use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::lowerer::{Lowerer, VariablesLowererInterface},
};
use vir_crate::{
    common::expression::{ExpressionIterator, UnaryOperationHelpers},
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super) trait BlockMarkersInterface {
    fn create_block_marker(
        &mut self,
        label: &vir_mid::BasicBlockId,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn lower_block_marker_condition(
        &mut self,
        condition: vir_mid::BlockMarkerCondition,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> BlockMarkersInterface for Lowerer<'p, 'v, 'tcx> {
    fn create_block_marker(
        &mut self,
        label: &vir_mid::BasicBlockId,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        self.create_variable(format!("{}$marker", label), vir_low::Type::Bool)
    }
    fn lower_block_marker_condition(
        &mut self,
        condition: vir_mid::BlockMarkerCondition,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mut conjuncts: Vec<vir_low::Expression> = Vec::new();
        for element in condition.elements {
            let marker = self.create_block_marker(&element.basic_block_id)?;
            let condition = if element.visited {
                marker.into()
            } else {
                vir_low::Expression::not(marker.into())
            };
            conjuncts.push(condition);
        }
        Ok(conjuncts.into_iter().conjoin())
    }
}
