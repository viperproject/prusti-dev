// FIXME: Rename the module.

use super::super::PredicateKind;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        lowerer::Lowerer,
        places::PlacesInterface,
        predicates::PredicatesOwnedInterface,
        snapshots::{IntoSnapshotLowerer, SnapshotVariablesInterface},
    },
};

use vir_crate::{
    common::position::Positioned,
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

pub(in super::super::super::super::super) struct PlaceToSnapshot {
    old_label: Option<String>,
    predicate_kind: PredicateKind,
}

impl PlaceToSnapshot {
    pub(in super::super::super::super) fn for_place(predicate_kind: PredicateKind) -> Self {
        Self {
            old_label: None,
            predicate_kind,
        }
    }

    fn snap_call<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        ty: &vir_mid::Type,
        pointer_place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let place = lowerer.encode_expression_as_place(pointer_place)?;
        let address = lowerer.encode_expression_as_place_address(pointer_place)?;
        match &self.predicate_kind {
            PredicateKind::Owned => lowerer.owned_non_aliased_snap(
                CallContext::Procedure,
                ty,
                ty,
                place,
                address,
                pointer_place.position(),
            ),
            PredicateKind::FracRef { lifetime } => {
                let TODO_target_slice_len = None;
                lowerer.frac_ref_snap(
                    CallContext::Procedure,
                    ty,
                    ty,
                    place,
                    address,
                    lifetime.clone(),
                    TODO_target_slice_len,
                    pointer_place.position(),
                )
            }
            PredicateKind::UniqueRef { lifetime, is_final } => {
                let TODO_target_slice_len = None;
                lowerer.unique_ref_snap(
                    CallContext::Procedure,
                    ty,
                    ty,
                    place,
                    address,
                    lifetime.clone(),
                    TODO_target_slice_len,
                    *is_final,
                    pointer_place.position(),
                )
            }
        }
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> IntoSnapshotLowerer<'p, 'v, 'tcx> for PlaceToSnapshot {
    fn expression_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        expression: &vir_mid::Expression,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(expression.is_place(),);
        let ty = expression.get_type();
        self.snap_call(lowerer, ty, expression)
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
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _old: &vir_mid::LabelledOld,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn func_app_to_snapshot(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _app: &vir_mid::FuncApp,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn acc_predicate_to_snapshot(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _acc_predicate: &vir_mid::AccPredicate,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn call_context(&self) -> CallContext {
        todo!()
    }

    fn owned_non_aliased_snap(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _ty: &vir_mid::Type,
        _pointer_place: &vir_mid::Expression,
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

    fn push_bound_variables(
        &mut self,
        _variables: &[vir_mid::VariableDecl],
    ) -> SpannedEncodingResult<()> {
        todo!()
    }

    fn pop_bound_variables(&mut self) -> SpannedEncodingResult<()> {
        todo!()
    }
}
