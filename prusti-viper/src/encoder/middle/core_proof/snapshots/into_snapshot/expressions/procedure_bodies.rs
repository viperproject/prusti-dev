use super::super::PredicateKind;
use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        footprint::FootprintInterface,
        lowerer::{FunctionsLowererInterface, Lowerer},
        places::PlacesInterface,
        pointers::PointersInterface,
        predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface},
        snapshots::{IntoSnapshotLowerer, SnapshotValuesInterface, SnapshotVariablesInterface},
    },
};
use rustc_hash::FxHashMap;
use vir_crate::{
    common::{identifier::WithIdentifier, position::Positioned},
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

pub(in super::super::super::super::super) struct ProcedureExpressionToSnapshot {
    old_label: Option<String>,
    predicate_kind: PredicateKind,
    /// If `true`, uses SSA snapshots instead of `snap` calls for stack
    /// variables.
    use_pure_stack: bool,
}

impl ProcedureExpressionToSnapshot {
    pub(in super::super::super::super) fn for_address(predicate_kind: PredicateKind) -> Self {
        Self {
            old_label: None,
            predicate_kind,
            use_pure_stack: true,
        }
    }

    pub(in super::super::super::super) fn for_place(predicate_kind: PredicateKind) -> Self {
        Self {
            old_label: None,
            predicate_kind,
            use_pure_stack: false,
        }
    }

    fn snap_call<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        ty: &vir_mid::Type,
        pointer_place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let place = lowerer.encode_expression_as_place(pointer_place)?;
        let root_address = lowerer.extract_root_address(pointer_place)?;
        match &self.predicate_kind {
            PredicateKind::Owned => lowerer.owned_non_aliased_snap(
                CallContext::Procedure,
                ty,
                ty,
                place,
                root_address,
                pointer_place.position(),
            ),
            PredicateKind::FracRef { lifetime } => {
                let TODO_target_slice_len = None;
                lowerer.frac_ref_snap(
                    CallContext::Procedure,
                    ty,
                    ty,
                    place,
                    root_address,
                    lifetime.clone(),
                    TODO_target_slice_len,
                )
            }
            PredicateKind::UniqueRef { lifetime, is_final } => {
                let TODO_target_slice_len = None;
                lowerer.unique_ref_snap(
                    CallContext::Procedure,
                    ty,
                    ty,
                    place,
                    root_address,
                    lifetime.clone(),
                    TODO_target_slice_len,
                    *is_final,
                )
            }
        }
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> IntoSnapshotLowerer<'p, 'v, 'tcx> for ProcedureExpressionToSnapshot {
    fn expression_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        expression: &vir_mid::Expression,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(
            expression.is_place(),
            "FIXME: Should this be renamed to place encoder and accept only places?"
        );
        if lowerer.check_mode.unwrap().check_core_proof() {
            // In the core proof checking mode, all places are obtained by
            // applying the snap functions. To make the results predictable
            // we always call the snap function on the place that the user
            // wrote.
            if self.use_pure_stack {
                // This is a hack for addresses. See `Prusti places` HackMD for
                // details.
                if expression.get_last_dereferenced_pointer().is_some() {
                    let ty = expression.get_type();
                    self.snap_call(lowerer, ty, expression)
                } else {
                    self.expression_to_snapshot_impl(lowerer, expression, expect_math_bool)
                }
            } else {
                let ty = expression.get_type();
                self.snap_call(lowerer, ty, expression)
            }
        } else {
            self.expression_to_snapshot_impl(lowerer, expression, expect_math_bool)
        }
    }

    fn variable_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        if let Some(label) = &self.old_label {
            lowerer.snapshot_variable_version_at_label(variable, label)
        } else {
            lowerer.current_snapshot_variable_version(variable)
        }
    }

    fn labelled_old_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        old: &vir_mid::LabelledOld,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn func_app_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        app: &vir_mid::FuncApp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn acc_predicate_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        acc_predicate: &vir_mid::AccPredicate,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn call_context(&self) -> CallContext {
        todo!()
    }

    fn owned_non_aliased_snap(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        ty: &vir_mid::Type,
        pointer_place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn pointer_deref_to_snapshot(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _deref: &vir_mid::Deref,
        _base_snapshot: vir_low::Expression,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        unreachable!("Should be overriden.");
    }
}
