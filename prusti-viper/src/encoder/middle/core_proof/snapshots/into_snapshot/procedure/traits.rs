//! Public facing traits.

use super::ProcedureSnapshot;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{lowerer::Lowerer, snapshots::into_snapshot::common::IntoSnapshotLowerer},
};
use vir_crate::{
    low::{self as vir_low},
    middle::{self as vir_mid},
};

/// Converts `self` into expression that evaluates to a Viper Bool.
pub(in super::super::super::super) trait IntoProcedureBoolExpression {
    type Target;
    fn to_procedure_bool_expression<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target>;
}

impl IntoProcedureBoolExpression for vir_mid::Expression {
    type Target = vir_low::Expression;
    fn to_procedure_bool_expression<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        ProcedureSnapshot::default().expression_to_snapshot(lowerer, self, true)
    }
}

pub(in super::super::super::super) trait IntoProcedureSnapshot {
    type Target;
    fn to_procedure_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target>;
}

impl IntoProcedureSnapshot for vir_mid::VariableDecl {
    type Target = vir_low::VariableDecl;
    fn to_procedure_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        ProcedureSnapshot::default().variable_to_snapshot(lowerer, self)
    }
}

impl IntoProcedureSnapshot for vir_mid::Expression {
    type Target = vir_low::Expression;
    fn to_procedure_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        ProcedureSnapshot::default().expression_to_snapshot(lowerer, self, false)
    }
}

impl<T: IntoProcedureSnapshot> IntoProcedureSnapshot for Vec<T> {
    type Target = Vec<T::Target>;
    fn to_procedure_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        let mut snapshots = Vec::new();
        for element in self {
            snapshots.push(element.to_procedure_snapshot(lowerer)?);
        }
        Ok(snapshots)
    }
}

pub(in super::super::super::super) trait IntoProcedureFinalSnapshot {
    type Target;
    fn to_procedure_final_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target>;
}

impl IntoProcedureFinalSnapshot for vir_mid::Expression {
    type Target = vir_low::Expression;
    fn to_procedure_final_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        let mut snapshot_encoder = ProcedureSnapshot {
            deref_to_final: true,
            ..ProcedureSnapshot::default()
        };
        snapshot_encoder.expression_to_snapshot(lowerer, self, false)
    }
}
