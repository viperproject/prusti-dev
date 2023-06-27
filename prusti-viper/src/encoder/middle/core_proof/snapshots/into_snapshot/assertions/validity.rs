use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext,
        footprint::{DerefFields, DerefOwned, DerefOwnedRange},
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
    framed_range_addresses: Vec<vir_mid::Expression>,
    deref_range_fields: BTreeMap<vir_mid::Expression, vir_low::VariableDecl>,
}

impl ValidityAssertionToSnapshot {
    pub(in super::super::super::super) fn new(
        (deref_fields, deref_range_fields): DerefFields,
    ) -> Self {
        Self {
            framed_places: Vec::new(),
            deref_fields: deref_fields
                .into_iter()
                .map(
                    |DerefOwned {
                         place,
                         field_name,
                         field_type,
                     }| {
                        (place, vir_low::VariableDecl::new(field_name, field_type))
                    },
                )
                .collect(),
            framed_range_addresses: Vec::new(),
            deref_range_fields: deref_range_fields
                .into_iter()
                .map(
                    |DerefOwnedRange {
                         address,
                         field_name,
                         field_type,
                     }| {
                        (address, vir_low::VariableDecl::new(field_name, field_type))
                    },
                )
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
            // for framed_place in &self.framed_places {
            //     eprintln!("Framed: {framed_place}");
            // }
            assert!(
                self.framed_places.contains(expression),
                "The place {expression} must be framed"
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
        assert!(variable.is_self_variable(), "{variable} must be self");
        Ok(vir_low::VariableDecl {
            name: variable.name.clone(),
            ty: self.type_to_snapshot(lowerer, &variable.ty)?,
        })
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
            vir_mid::Predicate::OwnedRange(predicate) => {
                self.framed_range_addresses.push(predicate.address.clone());
                let address = self.expression_to_snapshot(lowerer, &predicate.address, false)?;
                self.framed_range_addresses.pop();
                lowerer
                    .encode_snapshot_valid_call_for_type(address, predicate.address.get_type())?
            }
            vir_mid::Predicate::MemoryBlockHeap(_)
            | vir_mid::Predicate::MemoryBlockHeapRange(_)
            | vir_mid::Predicate::MemoryBlockHeapDrop(_) => true.into(),
            _ => unimplemented!("{acc_predicate}"),
        };
        Ok(expression)
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
