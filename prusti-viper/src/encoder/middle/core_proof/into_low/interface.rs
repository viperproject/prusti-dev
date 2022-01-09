use super::MidCoreProofEncoderInterface;
use crate::encoder::{
    errors::{BuiltinMethodKind, ErrorCtxt, SpannedEncodingResult},
    high::{type_layouts::HighTypeLayoutsEncoderInterface, types::HighTypeEncoderInterface},
    middle::core_proof::{
        addresses::AddressesInterface,
        compute_address::ComputeAddressInterface,
        errors::ErrorsInterface,
        fold_unfold::FoldUnfoldInterface,
        lowerer::{FunctionsLowererInterface, Lowerer, MethodsLowererInterface},
        predicates_memory_block::PredicatesMemoryBlockInterface,
        predicates_owned::PredicatesOwnedInterface,
        snapshots::{IntoSnapshot, SnapshotsInterface},
    },
    Encoder,
};
use rustc_data_structures::fx::FxHashSet;
use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
};
use vir_crate::{
    common::{
        expression::{ExpressionIterator, QuantifierHelpers},
        identifier::WithIdentifier,
    },
    low as vir_low, middle as vir_mid,
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
