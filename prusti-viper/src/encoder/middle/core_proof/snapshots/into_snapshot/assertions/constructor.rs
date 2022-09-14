use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext,
        footprint::{DerefFields, DerefOwned, DerefOwnedRange},
        lowerer::{DomainsLowererInterface, Lowerer},
        places::PlacesInterface,
        pointers::PointersInterface,
        predicates::PredicatesOwnedInterface,
        snapshots::{
            IntoSnapshot, IntoSnapshotLowerer, SnapshotDomainsInterface, SnapshotValuesInterface,
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
    /// Mapping from deref range fields to their positions in the arguments' list.
    deref_range_fields: BTreeMap<usize, vir_mid::Expression>,
    /// Which places are framed on the path being explored.
    framed_places: Vec<vir_mid::Expression>,
    /// Which addresses are framed on the path being explored.
    ///
    /// The tuple is `(address, start_index, end_index)`.
    framed_range_addresses: Vec<(
        vir_mid::Expression,
        vir_mid::Expression,
        vir_mid::Expression,
    )>,
    /// Whether should wrap all snap calls into old.
    is_in_old_state: bool,
    /// A flag used to check whether a conditional has nested conditionals.
    found_conditional: bool,
    position: vir_low::Position,
}

fn deref_fields_into_maps(
    regular_field_arguments_len: usize,
    (deref_fields, deref_range_fields): DerefFields,
) -> (
    BTreeMap<usize, vir_mid::Expression>,
    BTreeMap<usize, vir_mid::Expression>,
) {
    let deref_fields = deref_fields
        .into_iter()
        .enumerate()
        .map(|(i, DerefOwned { place, .. })| (i + regular_field_arguments_len, place))
        .collect::<BTreeMap<_, _>>();
    let deref_range_fields = deref_range_fields
        .into_iter()
        .enumerate()
        .map(|(i, DerefOwnedRange { address, .. })| {
            (
                i + deref_fields.len() + regular_field_arguments_len,
                address,
            )
        })
        .collect();
    (deref_fields, deref_range_fields)
}

impl<'a> AssertionToSnapshotConstructor<'a> {
    pub(in super::super::super::super) fn for_assign_aggregate_postcondition(
        ty: &'a vir_mid::Type,
        regular_field_arguments: Vec<vir_low::Expression>,
        fields: Vec<vir_mid::FieldDecl>,
        all_deref_fields: DerefFields,
        position: vir_low::Position,
    ) -> Self {
        let field_replacement_map = fields
            .into_iter()
            .zip(regular_field_arguments.iter().cloned())
            .collect();
        let (deref_fields, deref_range_fields) =
            deref_fields_into_maps(regular_field_arguments.len(), all_deref_fields);
        Self {
            predicate_kind: PredicateKind::Owned,
            ty,
            regular_field_arguments,
            field_replacement_map,
            deref_fields,
            deref_range_fields,
            framed_places: Vec::new(),
            framed_range_addresses: Vec::new(),
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
        all_deref_fields: DerefFields,
        position: vir_low::Position,
    ) -> Self {
        let field_replacement_map = fields
            .into_iter()
            .zip(regular_field_arguments.iter().cloned())
            .collect();
        let (deref_fields, deref_range_fields) =
            deref_fields_into_maps(regular_field_arguments.len(), all_deref_fields);
        Self {
            predicate_kind,
            ty,
            regular_field_arguments,
            field_replacement_map,
            deref_fields,
            deref_range_fields,
            framed_places: Vec::new(),
            framed_range_addresses: Vec::new(),
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
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        match &self.predicate_kind {
            PredicateKind::Owned => lowerer.owned_non_aliased_snap(
                CallContext::BuiltinMethod,
                ty,
                ty,
                place,
                address,
                position,
            ),
            PredicateKind::FracRef { lifetime } => {
                let TODO_target_slice_len = None;
                lowerer.frac_ref_snap(
                    CallContext::BuiltinMethod,
                    ty,
                    ty,
                    place,
                    address,
                    lifetime.clone(),
                    TODO_target_slice_len,
                    position,
                )
            }
            PredicateKind::UniqueRef { lifetime, is_final } => {
                let TODO_target_slice_len = None;
                lowerer.unique_ref_snap(
                    CallContext::BuiltinMethod,
                    ty,
                    ty,
                    place,
                    address,
                    lifetime.clone(),
                    TODO_target_slice_len,
                    *is_final,
                    position,
                )
            }
        }
    }

    fn snap_range_call<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        ty: &vir_mid::Type,
        address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        match &self.predicate_kind {
            PredicateKind::Owned => lowerer.owned_aliased_range_snap(
                CallContext::BuiltinMethod,
                ty,
                ty,
                address,
                start_index,
                end_index,
                position,
            ),
            PredicateKind::FracRef { lifetime } => lowerer.frac_ref_range_snap(
                CallContext::BuiltinMethod,
                ty,
                ty,
                address,
                start_index,
                end_index,
                lifetime.clone(),
                position,
            ),
            PredicateKind::UniqueRef { lifetime, is_final } => lowerer.unique_ref_range_snap(
                CallContext::BuiltinMethod,
                ty,
                ty,
                address,
                start_index,
                end_index,
                lifetime.clone(),
                *is_final,
                position,
            ),
        }
    }

    fn generate_dangling_snapshot<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let domain_name = lowerer.encode_snapshot_domain_name(ty)?;
        let function_name = format!("{domain_name}$dangling");
        let return_type = ty.to_snapshot(lowerer)?;
        lowerer.create_unique_domain_func_app(
            domain_name,
            function_name,
            Vec::new(),
            return_type,
            self.position,
        )
    }

    fn compute_deref_address<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let address = match place {
            vir_mid::Expression::Local(_) => unreachable!("{place}"),
            vir_mid::Expression::Field(_) => todo!(),
            vir_mid::Expression::Deref(deref) => {
                let base_snapshot = self.expression_to_snapshot(lowerer, &deref.base, true)?;
                let ty = deref.base.get_type();
                lowerer.pointer_address(ty, base_snapshot, place.position())?
            }
            _ => unimplemented!("{place}"),
        };
        Ok(address)
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
                let place = lowerer.encode_expression_as_place(deref_field)?;
                // Note: we cannot use `encode_expression_as_place_address` here
                // because that method can be used only inside procedure with
                // SSA addresses. Therefore, we need to compute the address
                // ourselves.
                let address = self.compute_deref_address(lowerer, deref_field)?;
                let snap_call = self.snap_call(lowerer, ty, place, address, self.position)?;
                if self.is_in_old_state {
                    vir_low::Expression::labelled_old(None, snap_call, self.position)
                } else {
                    snap_call
                }
            } else {
                // The place is not framed. Create a dangling (null) snapshot.
                self.generate_dangling_snapshot(lowerer, ty)?
            };
            arguments.push(deref_field_snapshot);
        }
        for deref_range_field in self.deref_range_fields.clone().values() {
            let ty = deref_range_field.get_type();
            let deref_range_field_snapshot =
                if let Some((pointer_value_mid, start_index, end_index)) = self
                    .framed_range_addresses
                    .iter()
                    .find(|(address, _, _)| deref_range_field == address)
                    .cloned()
                {
                    // The address is framed, generate the snap call.
                    let pointer_value =
                        self.expression_to_snapshot(lowerer, &pointer_value_mid, true)?;
                    let start_index = self.expression_to_snapshot(lowerer, &start_index, true)?;
                    let end_index = self.expression_to_snapshot(lowerer, &end_index, true)?;
                    let snap_call = self.snap_range_call(
                        lowerer,
                        ty,
                        pointer_value,
                        start_index,
                        end_index,
                        self.position,
                    )?;
                    if self.is_in_old_state {
                        vir_low::Expression::labelled_old(None, snap_call, self.position)
                    } else {
                        snap_call
                    }
                } else {
                    // The place is not framed. Create a dangling (null) snapshot.
                    self.generate_dangling_snapshot(lowerer, ty)?
                };
            arguments.push(deref_range_field_snapshot);
        }
        lowerer.construct_struct_snapshot(self.ty, arguments, self.position)
    }

    // // FIXME: Code duplication.
    // fn pointer_deref_into_address<'p, 'v, 'tcx>(
    //     &mut self,
    //     lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    //     place: &vir_mid::Expression,
    // ) -> SpannedEncodingResult<vir_low::Expression> {
    //     if let Some(deref_place) = place.get_last_dereferenced_pointer() {
    //         let base_snapshot = self.expression_to_snapshot(lowerer, deref_place, true)?;
    //         let ty = deref_place.get_type();
    //         lowerer.pointer_address(ty, base_snapshot, place.position())
    //     } else {
    //         unreachable!()
    //     }
    // }

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
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        todo!()
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
            vir_mid::Predicate::OwnedRange(predicate) => {
                self.framed_range_addresses.push((
                    predicate.address.clone(),
                    predicate.start_index.clone(),
                    predicate.end_index.clone(),
                ));
            }
            vir_mid::Predicate::OwnedSet(_) => todo!(),
            vir_mid::Predicate::UniqueRef(_) => todo!(),
            vir_mid::Predicate::UniqueRefRange(_) => todo!(),
            vir_mid::Predicate::FracRef(_) => todo!(),
            vir_mid::Predicate::FracRefRange(_) => todo!(),
        }
        Ok(true.into())
    }

    // FIXME: Code duplication.
    fn pointer_deref_to_snapshot(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _deref: &vir_mid::Deref,
        _base_snapshot: vir_low::Expression,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        unimplemented!("outdated code");
        // let heap = self
        //     .heap
        //     .clone()
        //     .expect("This function should be reachable only when heap is Some");
        // lowerer.pointer_target_snapshot_in_heap(
        //     deref.base.get_type(),
        //     heap,
        //     base_snapshot,
        //     deref.position,
        // )
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
