//! Public facing traits.

use super::ContextIndependentSnapshot;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{lowerer::Lowerer, snapshots::into_snapshot::common::IntoSnapshotLowerer},
};
use vir_crate::{
    low::{self as vir_low},
    middle::{self as vir_mid},
};

pub(in super::super::super::super) trait IntoSnapshot {
    type Target;
    fn to_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target>;
}

impl IntoSnapshot for vir_mid::UnaryOpKind {
    type Target = vir_low::expression::UnaryOpKind;
    fn to_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        ContextIndependentSnapshot.unary_op_kind_to_snapshot(lowerer, self)
    }
}

impl IntoSnapshot for vir_mid::BinaryOpKind {
    type Target = vir_low::expression::BinaryOpKind;
    fn to_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        ContextIndependentSnapshot.binary_op_kind_to_snapshot(lowerer, self)
    }
}

impl IntoSnapshot for vir_mid::Type {
    type Target = vir_low::Type;
    fn to_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        ContextIndependentSnapshot.type_to_snapshot(lowerer, self)
    }
}
