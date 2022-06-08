use super::BuiltinMethodSnapshot;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{lowerer::Lowerer, snapshots::into_snapshot::common::IntoSnapshotLowerer},
};
use vir_crate::{
    low::{self as vir_low},
    middle::{self as vir_mid},
};

/// Converts `self` into expression that evaluates to a snapshot.
pub(in super::super::super::super) trait IntoBuiltinMethodSnapshot {
    type Target;
    fn to_builtin_method_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target>;
}

impl IntoBuiltinMethodSnapshot for vir_mid::Expression {
    type Target = vir_low::Expression;
    fn to_builtin_method_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        BuiltinMethodSnapshot.expression_to_snapshot(lowerer, self, false)
    }
}
