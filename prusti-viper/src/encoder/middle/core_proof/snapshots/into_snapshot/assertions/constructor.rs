use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        lowerer::{DomainsLowererInterface, Lowerer},
        places::PlacesInterface,
        pointers::PointersInterface,
        predicates::PredicatesOwnedInterface,
        snapshots::{
            IntoSnapshot, IntoSnapshotLowerer, SnapshotDomainsInterface, SnapshotValidityInterface,
            SnapshotValuesInterface,
        },
    },
};
use rustc_hash::FxHashMap;
use std::collections::BTreeMap;
use vir_crate::{
    common::position::Positioned,
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

use super::PredicateKind;

pub(in super::super::super::super) struct AssertionToSnapshotConstructor<'a> {
    predicate_kind: PredicateKind,
    ty: &'a vir_mid::Type,
    /// Arguments for the regular struct fields.
    regular_field_arguments: Vec<vir_low::Expression>,
    /// A map for replacing `self.field` with a matching argument. Used in
    /// assign postcondition.
    field_replacement_map: FxHashMap<vir_mid::FieldDecl, vir_low::Expression>,
    /// Mapping from deref fields to their positions in the arguments' list.
    deref_fields: BTreeMap<usize, vir_mid::Expression>,
    /// Which places are framed on the path being explored.
    framed_places: Vec<vir_mid::Expression>,
    /// If Some, uses the heap variable instead of snap functions.
    heap: Option<vir_low::VariableDecl>,
    /// Whether should wrap all snap calls into old.
    is_in_old_state: bool,
    /// A flag used to check whether a conditional has nested conditionals.
    found_conditional: bool,
    position: vir_low::Position,
}

impl<'a> AssertionToSnapshotConstructor<'a> {
    pub(in super::super::super::super) fn for_assign_aggregate_postcondition(
        ty: &'a vir_mid::Type,
        regular_field_arguments: Vec<vir_low::Expression>,
        fields: Vec<vir_mid::FieldDecl>,
        deref_fields: Vec<(vir_mid::Expression, String, vir_low::Type)>,
        heap: Option<vir_low::VariableDecl>,
        position: vir_low::Position,
    ) -> Self {
        let field_replacement_map = fields
            .into_iter()
            .zip(regular_field_arguments.iter().cloned())
            .collect();
        let deref_fields = deref_fields
            .into_iter()
            .enumerate()
            .map(|(i, (e, _, _))| (i + regular_field_arguments.len(), e))
            .collect();
        Self {
            predicate_kind: PredicateKind::Owned,
            ty,
            regular_field_arguments,
            field_replacement_map,
            deref_fields,
            framed_places: Vec::new(),
            heap,
            is_in_old_state: true,
            found_conditional: false,
            position,
        }
    }

    pub(in super::super::super::super) fn for_function_body(
        predicate_kind: PredicateKind,
        ty: &'a vir_mid::Type,
        regular_field_arguments: Vec<vir_low::Expression>,
        fields: Vec<vir_mid::FieldDecl>,
        deref_fields: Vec<(vir_mid::Expression, String, vir_low::Type)>,
        position: vir_low::Position,
    ) -> Self {
        let field_replacement_map = fields
            .into_iter()
            .zip(regular_field_arguments.iter().cloned())
            .collect();
        let deref_fields = deref_fields
            .into_iter()
            .enumerate()
            .map(|(i, (e, _, _))| (i + regular_field_arguments.len(), e))
            .collect();
        Self {
            predicate_kind,
            ty,
            regular_field_arguments,
            field_replacement_map,
            deref_fields,
            framed_places: Vec::new(),
            heap: None,
            is_in_old_state: false,
            found_conditional: false,
            position,
        }
    }

    pub(in super::super::super::super) fn expression_to_snapshot_constructor<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        expression: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let constructor_expression = self.expression_to_snapshot(lowerer, expression, true)?;
        if self.found_conditional {
            Ok(constructor_expression)
        } else {
            self.generate_snapshot_constructor(lowerer)
        }
    }

    // FIXME: Code duplication.
    fn snap_call<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        ty: &vir_mid::Type,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        match &self.predicate_kind {
            PredicateKind::Owned => lowerer.owned_non_aliased_snap(
                CallContext::BuiltinMethod,
                ty,
                ty,
                place,
                root_address,
                position,
            ),
            PredicateKind::FracRef { lifetime } => {
                let TODO_target_slice_len = None;
                lowerer.frac_ref_snap(
                    CallContext::BuiltinMethod,
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
                    CallContext::BuiltinMethod,
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

    fn generate_snapshot_constructor<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mut arguments = self.regular_field_arguments.clone();
        for deref_field in self.deref_fields.clone().values() {
            let ty = deref_field.get_type();
            let deref_field_snapshot = if self.framed_places.contains(deref_field) {
                // The place is framed, generate the snap call.
                if self.heap.is_some() {
                    self.expression_to_snapshot(lowerer, deref_field, false)?
                } else {
                    let place = lowerer.encode_expression_as_place(deref_field)?;
                    let root_address = self.pointer_deref_into_address(lowerer, deref_field)?;
                    let snap_call =
                        self.snap_call(lowerer, ty, place, root_address, self.position)?;
                    // let snap_call = lowerer.owned_non_aliased_snap(
                    //     CallContext::BuiltinMethod,
                    //     ty,
                    //     ty,
                    //     place,
                    //     root_address,
                    //     self.position,
                    // )?;
                    if self.is_in_old_state {
                        vir_low::Expression::labelled_old(None, snap_call, self.position)
                    } else {
                        snap_call
                    }
                }
            } else {
                // The place is not framed. Create a dangling (null) snapshot.
                let domain_name = lowerer.encode_snapshot_domain_name(ty)?;
                let function_name = format!("{}$dangling", domain_name);
                let return_type = ty.to_snapshot(lowerer)?;
                lowerer.create_unique_domain_func_app(
                    domain_name,
                    function_name,
                    Vec::new(),
                    return_type,
                    self.position,
                )?
            };
            arguments.push(deref_field_snapshot);
        }
        lowerer.construct_struct_snapshot(self.ty, arguments, self.position)
    }

    // FIXME: Code duplication.
    fn pointer_deref_into_address<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if let Some(deref_place) = place.get_last_dereferenced_pointer() {
            let base_snapshot = self.expression_to_snapshot(lowerer, deref_place, true)?;
            let ty = deref_place.get_type();
            lowerer.pointer_address(ty, base_snapshot, place.position())
        } else {
            unreachable!()
        }
    }

    fn conditional_branch_to_snapshot<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        branch: &vir_mid::Expression,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.found_conditional = false;
        let old_framed_places_count = self.framed_places.len();
        let branch_snapshot = self.expression_to_snapshot(lowerer, branch, expect_math_bool)?;
        let expression = if !self.found_conditional {
            // We reached the lowest level, generate the snapshot constructor.
            self.generate_snapshot_constructor(lowerer)?
        } else {
            branch_snapshot
        };
        self.framed_places.truncate(old_framed_places_count);
        Ok(expression)
    }
}

impl<'a, 'p, 'v: 'p, 'tcx: 'v> IntoSnapshotLowerer<'p, 'v, 'tcx>
    for AssertionToSnapshotConstructor<'a>
{
    fn conditional_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        conditional: &vir_mid::Conditional,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let guard_snapshot = self.expression_to_snapshot(lowerer, &conditional.guard, true)?;

        let then_expr_snapshot =
            self.conditional_branch_to_snapshot(lowerer, &conditional.then_expr, expect_math_bool)?;
        let else_expr_snapshot =
            self.conditional_branch_to_snapshot(lowerer, &conditional.else_expr, expect_math_bool)?;

        self.found_conditional = true;
        Ok(vir_low::Expression::conditional(
            guard_snapshot,
            then_expr_snapshot,
            else_expr_snapshot,
            conditional.position,
        ))
    }

    fn field_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        field: &vir_mid::Field,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        match &*field.base {
            vir_mid::Expression::Local(local)
                if local.variable.is_self_variable()
                    && self.field_replacement_map.contains_key(&field.field) =>
            {
                Ok(self.field_replacement_map[&field.field].clone())
            }
            _ => self.field_to_snapshot_impl(lowerer, field, expect_math_bool),
        }
    }

    fn variable_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        todo!()
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
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        acc_predicate: &vir_mid::AccPredicate,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        match &*acc_predicate.predicate {
            vir_mid::Predicate::LifetimeToken(_)
            | vir_mid::Predicate::MemoryBlockStack(_)
            | vir_mid::Predicate::MemoryBlockStackDrop(_) => {
                unreachable!();
            }
            vir_mid::Predicate::MemoryBlockHeap(_)
            | vir_mid::Predicate::MemoryBlockHeapRange(_)
            | vir_mid::Predicate::MemoryBlockHeapDrop(_) => {
                // Do nothing.
            }
            vir_mid::Predicate::OwnedNonAliased(predicate) => {
                self.framed_places.push(predicate.place.clone());
            }
            vir_mid::Predicate::OwnedRange(_) => todo!(),
            vir_mid::Predicate::OwnedSet(_) => todo!(),
        }
        Ok(true.into())
    }

    // FIXME: Code duplication.
    fn pointer_deref_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        deref: &vir_mid::Deref,
        base_snapshot: vir_low::Expression,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let heap = self
            .heap
            .clone()
            .expect("This function should be reachable only when heap is Some");
        lowerer.pointer_target_snapshot_in_heap(
            deref.base.get_type(),
            heap,
            base_snapshot,
            deref.position,
        )
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
