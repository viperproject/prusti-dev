use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext,
        lowerer::Lowerer,
        snapshots::{IntoSnapshotLowerer, SnapshotValidityInterface},
    },
};
use std::collections::BTreeMap;
use vir_crate::{
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

pub(in super::super::super::super::super) struct ValidityAssertionToSnapshot {
    framed_places: Vec<vir_mid::Expression>,
    deref_fields: BTreeMap<vir_mid::Expression, vir_low::VariableDecl>,
}

impl ValidityAssertionToSnapshot {
    pub(in super::super::super::super::super) fn new(
        deref_fields: Vec<(vir_mid::Expression, String, vir_low::Type)>,
    ) -> Self {
        Self {
            framed_places: Vec::new(),
            deref_fields: deref_fields
                .into_iter()
                .map(|(owned_place, name, ty)| (owned_place, vir_low::VariableDecl::new(name, ty)))
                .collect(),
        }
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> IntoSnapshotLowerer<'p, 'v, 'tcx> for ValidityAssertionToSnapshot {
    fn expression_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        expression: &vir_mid::Expression,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if let Some(field) = self.deref_fields.get(expression) {
            assert!(
                self.framed_places.contains(expression),
                "The place {} must be framed",
                expression
            );
            Ok(field.clone().into())
        } else {
            self.expression_to_snapshot_impl(lowerer, expression, expect_math_bool)
        }
    }

    fn variable_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        assert!(variable.is_self_variable(), "{} must be self", variable);
        Ok(vir_low::VariableDecl {
            name: variable.name.clone(),
            ty: self.type_to_snapshot(lowerer, &variable.ty)?,
        })
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

    fn binary_op_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        op: &vir_mid::BinaryOp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mut introduced_snap = false;
        if op.op_kind == vir_mid::BinaryOpKind::And {
            if let box vir_mid::Expression::AccPredicate(expression) = &op.left {
                if let vir_mid::Predicate::OwnedNonAliased(predicate) = &*expression.predicate {
                    self.framed_places.push(predicate.place.clone());
                    introduced_snap = true;
                }
            }
        }
        let expression = self.binary_op_to_snapshot_impl(lowerer, op, expect_math_bool)?;
        if introduced_snap {
            self.framed_places.pop();
        }
        Ok(expression)
    }

    fn acc_predicate_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        acc_predicate: &vir_mid::AccPredicate,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(expect_math_bool);
        let expression = match &*acc_predicate.predicate {
            vir_mid::Predicate::OwnedNonAliased(predicate) => {
                self.framed_places.push(predicate.place.clone());
                let place = self.expression_to_snapshot(lowerer, &predicate.place, false)?;
                self.framed_places.pop();
                lowerer.encode_snapshot_valid_call_for_type(place, predicate.place.get_type())?
            }
            vir_mid::Predicate::MemoryBlockHeap(_) | vir_mid::Predicate::MemoryBlockHeapDrop(_) => {
                true.into()
            }
            _ => unimplemented!("{acc_predicate}"),
        };
        Ok(expression)
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
}
