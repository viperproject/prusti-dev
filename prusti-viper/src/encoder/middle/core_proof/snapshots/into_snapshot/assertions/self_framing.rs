use super::PredicateKind;
use crate::encoder::{
    errors::{SpannedEncodingError, SpannedEncodingResult},
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        lifetimes::LifetimesInterface,
        lowerer::{FunctionsLowererInterface, Lowerer},
        places::PlacesInterface,
        pointers::PointersInterface,
        predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface},
        snapshots::{IntoSnapshotLowerer, SnapshotValuesInterface, SnapshotVariablesInterface},
        type_layouts::TypeLayoutsInterface,
        utils::bound_variable_stack::{BoundVariableStack, BoundVariableStackMiddle},
    },
};
use rustc_hash::FxHashMap;
use std::collections::BTreeMap;
use vir_crate::{
    common::{identifier::WithIdentifier, position::Positioned},
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

#[derive(Clone, Debug, PartialEq, Eq, derive_more::IsVariant)]
enum CallerKind {
    PredicateBody {
        /// The `place` parameter of the predicate.
        place: vir_low::VariableDecl,
        /// The `address` parameter of the predicate.
        address: vir_low::VariableDecl,
    },
    AssignPrecondition {
        /// A map for replacing `self.field` with a matching argument.
        field_replacement_map: FxHashMap<vir_mid::FieldDecl, vir_low::Expression>,
    },
    InhaleExhale,
    // PlaceExpression,
}

#[derive(Default)]
pub(in super::super::super::super::super) struct SelfFramingAssertionEncoderState {
    states: BTreeMap<String, State>,
}

#[derive(Default)]
struct State {
    snap_calls: Vec<(vir_mid::Expression, vir_low::Expression)>,
    range_snap_calls: Vec<(vir_low::Expression, (vir_mid::Type, vir_low::Position))>,
}

// Based on
// prusti-viper/src/encoder/middle/core_proof/predicates/owned/builders/owned_non_aliased/predicate_decl.rs,
// whch should be deleted.
pub(in super::super::super::super::super) struct SelfFramingAssertionToSnapshot {
    /// Indicates which constructor was used. This is used only for assertions
    /// to ensure that certain branches are unreachable.
    caller_kind: CallerKind,
    /// Do we need to use SSA when encoding variables?
    use_ssa: bool,
    /// Which kind of predicate is being encoded?
    predicate_kind: PredicateKind,
    /// Keeps track of types for which we need to encode predicates.
    created_predicate_types: Vec<vir_mid::Type>,
    /// Mapping from place to snapshot. We use a vector because we need to know
    /// the insertion order.
    snap_calls: Vec<(vir_mid::Expression, vir_low::Expression)>,
    /// Mapping from the start of owned range to information needed to compute
    /// the snapshot of an element. We use a vector because we need to know the
    /// insertion order.
    range_snap_calls: Vec<(vir_low::Expression, (vir_mid::Type, vir_low::Position))>,
    /// If true, removes the accessibility predicates from the result.
    is_target_pure: bool,
    /// The old label in the currently converted subexpression.
    old_label: Option<String>,
    /// Variables introduced by quantifiers.
    bound_variable_stack: BoundVariableStack,
    /// The label of the current state in which information about `snap_calls`
    /// and `range_snap_calls` should be stored.
    ///
    /// This is used only for inhale and exhale statements.
    current_state_label: Option<String>,
}

impl SelfFramingAssertionToSnapshot {
    /// Used for encoding structural invariant as a predicate body.
    pub(in super::super::super::super::super) fn for_predicate_body(
        place: vir_low::VariableDecl,
        address: vir_low::VariableDecl,
        predicate_kind: PredicateKind,
    ) -> Self {
        Self {
            caller_kind: CallerKind::PredicateBody { place, address },
            use_ssa: false,
            predicate_kind,
            created_predicate_types: Vec::new(),
            snap_calls: Vec::new(),
            range_snap_calls: Vec::new(),
            is_target_pure: false,
            old_label: None,
            bound_variable_stack: Default::default(),
            current_state_label: None,
        }
    }

    /// Used for encoding structural invariant as a assign helper method
    /// postcondition.
    pub(in super::super::super::super::super) fn for_assign_precondition(
        regular_field_arguments: Vec<vir_low::Expression>,
        fields: Vec<vir_mid::FieldDecl>,
    ) -> Self {
        let field_replacement_map = fields
            .into_iter()
            .zip(regular_field_arguments.iter().cloned())
            .collect();
        Self {
            caller_kind: CallerKind::AssignPrecondition {
                field_replacement_map,
            },
            use_ssa: false,
            predicate_kind: PredicateKind::Owned,
            created_predicate_types: Vec::new(),
            snap_calls: Vec::new(),
            range_snap_calls: Vec::new(),
            is_target_pure: false,
            old_label: None,
            bound_variable_stack: Default::default(),
            current_state_label: None,
        }
    }

    /// Used for encoding inhale and exhale statements.
    pub(in super::super::super::super::super) fn for_inhale_exhale_expression(
        current_state_label: Option<String>,
    ) -> Self {
        Self {
            caller_kind: CallerKind::InhaleExhale,
            use_ssa: true,
            predicate_kind: PredicateKind::Owned,
            created_predicate_types: Vec::new(),
            snap_calls: Vec::new(),
            range_snap_calls: Vec::new(),
            is_target_pure: false,
            old_label: None,
            bound_variable_stack: Default::default(),
            current_state_label,
        }
    }

    // Use PlaceToSnapshot::for_place instead.
    // /// Used for encoding place expressions in procedures.
    // pub(in super::super::super::super::super) fn for_place_expression() -> Self {
    //     Self {
    //         caller_kind: CallerKind::PlaceExpression,
    //         use_ssa: true,
    //         predicate_kind: PredicateKind::Owned,
    //         created_predicate_types: Vec::new(),
    //         snap_calls: Vec::new(),
    //         range_snap_calls: Vec::new(),
    //         is_target_pure: false,
    //         old_label: None,
    //         bound_variable_stack: Default::default(),
    //         current_state_label: None,
    //     }
    // }

    pub(in super::super::super::super::super) fn into_created_predicate_types(
        self,
    ) -> Vec<vir_mid::Type> {
        self.created_predicate_types
    }

    fn predicate_place(&self) -> vir_low::Expression {
        let CallerKind::PredicateBody { ref place, .. } = self.caller_kind else {
            unreachable!()
        };
        place.clone().into()
    }

    fn predicate_address(&self) -> vir_low::Expression {
        let CallerKind::PredicateBody { ref address, .. } = self.caller_kind else {
            unreachable!()
        };
        address.clone().into()
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

    // FIXME: Code duplication.
    fn snap_call<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        ty: &vir_mid::Type,
        place: vir_low::Expression,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.snap_call_with_predicate_kind(
            lowerer,
            ty,
            self.predicate_kind.clone(),
            place,
            address,
            position,
        )
    }

    // FIXME: Code duplication.
    fn snap_call_with_predicate_kind<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        ty: &vir_mid::Type,
        predicate_kind: PredicateKind,
        place: vir_low::Expression,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        match predicate_kind {
            PredicateKind::Owned => lowerer.owned_non_aliased_snap(
                self.call_context(),
                ty,
                ty,
                place,
                address,
                position,
            ),
            PredicateKind::FracRef { lifetime } => {
                let TODO_target_slice_len = None;
                lowerer.frac_ref_snap(
                    self.call_context(),
                    ty,
                    ty,
                    place,
                    address,
                    lifetime,
                    TODO_target_slice_len,
                    position,
                )
            }
            PredicateKind::UniqueRef { lifetime, is_final } => {
                assert!(!is_final);
                let TODO_target_slice_len = None;
                lowerer.unique_ref_snap(
                    self.call_context(),
                    ty,
                    ty,
                    place,
                    address,
                    lifetime,
                    TODO_target_slice_len,
                    false,
                    position,
                )
            }
        }
    }

    fn predicate<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        ty: &vir_mid::Type,
        place: vir_low::Expression,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.created_predicate_types.push(ty.clone());
        match &self.predicate_kind {
            PredicateKind::Owned => lowerer.owned_non_aliased(
                self.call_context(),
                ty,
                ty,
                place,
                address,
                None,
                position,
            ),
            PredicateKind::FracRef { lifetime } => {
                let TODO_target_slice_len = None;
                lowerer.frac_ref(
                    self.call_context(),
                    ty,
                    ty,
                    place,
                    address,
                    lifetime.clone(),
                    TODO_target_slice_len,
                    None,
                    position,
                )
            }
            PredicateKind::UniqueRef { lifetime, is_final } => {
                assert!(!is_final);
                let TODO_target_slice_len = None;
                // let _final_snapshot = lowerer.unique_ref_snap(
                //     self.call_context(),
                //     ty,
                //     ty,
                //     place.clone(),
                //     address.clone(),
                //     lifetime.clone(),
                //     TODO_target_slice_len.clone(),
                //     true,
                //     position,
                // )?;
                lowerer.unique_ref(
                    self.call_context(),
                    ty,
                    ty,
                    place,
                    address,
                    lifetime.clone(),
                    TODO_target_slice_len,
                    None,
                    position,
                )
            }
        }
    }

    fn predicate_range<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        ty: &vir_mid::Type,
        address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.created_predicate_types.push(ty.clone());
        match &self.predicate_kind {
            PredicateKind::Owned => lowerer.owned_aliased_range(
                self.call_context(),
                ty,
                ty,
                address,
                start_index,
                end_index,
                None,
                position,
            ),
            PredicateKind::UniqueRef { lifetime, is_final } => {
                assert!(!is_final);
                lowerer.unique_ref_range(
                    self.call_context(),
                    ty,
                    ty,
                    address,
                    start_index,
                    end_index,
                    lifetime.clone(),
                    None,
                    position,
                )
            }
            PredicateKind::FracRef { lifetime } => lowerer.frac_ref_range(
                self.call_context(),
                ty,
                ty,
                address,
                start_index,
                end_index,
                lifetime.clone(),
                None,
                position,
            ),
        }
    }

    fn maybe_store_range_snap_call<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        address: &vir_low::Expression,
        ty: &vir_mid::Type,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        if let Some(current_state_label) = &self.current_state_label {
            let entry = lowerer
                .snapshots_state
                .self_framing_assertion_encoder_state
                .states
                .entry(current_state_label.clone())
                .or_default();
            entry
                .range_snap_calls
                .push((address.clone(), (ty.clone(), position)));
        }
        Ok(())
    }

    fn get_range_snap_calls<'a, 'p, 'v, 'tcx>(
        &'a self,
        lowerer: &'a mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<&'a [(vir_low::Expression, (vir_mid::Type, vir_low::Position))]>
    {
        if let Some(old_label) = &self.old_label {
            let entry = lowerer
                .snapshots_state
                .self_framing_assertion_encoder_state
                .states
                .get(old_label)
                .unwrap();
            Ok(&entry.range_snap_calls)
        } else {
            Ok(&self.range_snap_calls)
        }
    }

    fn maybe_store_snap_call<'p, 'v, 'tcx>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        place: &vir_mid::Expression,
        snap_call: &vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        if let Some(current_state_label) = &self.current_state_label {
            let entry = lowerer
                .snapshots_state
                .self_framing_assertion_encoder_state
                .states
                .entry(current_state_label.clone())
                .or_default();
            entry.snap_calls.push((place.clone(), snap_call.clone()));
        }
        Ok(())
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> IntoSnapshotLowerer<'p, 'v, 'tcx> for SelfFramingAssertionToSnapshot {
    fn expression_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        expression: &vir_mid::Expression,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        for (place, call) in &self.snap_calls {
            if place == expression {
                return self.ensure_bool_expression(
                    lowerer,
                    expression.get_type(),
                    call.clone(),
                    expect_math_bool,
                );
                // return Ok(call.clone());
            }
        }
        self.expression_to_snapshot_impl(lowerer, expression, expect_math_bool)
    }

    fn binary_op_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        op: &vir_mid::BinaryOp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // let mut introduced_snap = false;
        // let mut introduced_range_snap = false;
        // if op.op_kind == vir_mid::BinaryOpKind::And {
        //     if let box vir_mid::Expression::AccPredicate(expression) = &op.left {
        //         if expression.predicate.is_owned_non_aliased() {
        //             // The recursive call to `acc_predicate_to_snapshot` will
        //             // add a snap call to `self.snap_calls`.
        //             introduced_snap = true;
        //         }
        //         if expression.predicate.is_owned_range() {
        //             // The recursive call to `acc_predicate_to_snapshot` will
        //             // add a snap call to `self.range_snap_calls`.
        //             introduced_range_snap = true;
        //         }
        //     }
        // }
        let snap_call_count = self.snap_calls.len();
        let snap_range_call_count = self.range_snap_calls.len();
        let expression = self.binary_op_to_snapshot_impl(lowerer, op, expect_math_bool)?;
        if op.op_kind == vir_mid::BinaryOpKind::Implies {
            // The predicates were introduced conditionally and, therefore,
            // frame only the right hand side of the implication.
            while self.snap_calls.len() > snap_call_count {
                self.snap_calls.pop();
            }
            while self.range_snap_calls.len() > snap_range_call_count {
                self.range_snap_calls.pop();
            }
        }
        // if introduced_snap {
        //     self.snap_calls.pop();
        // }
        // if introduced_range_snap {
        //     let predicate = self.range_snap_calls.pop();
        //     eprintln!("pop: {:?}", predicate);
        // }
        Ok(expression)
    }

    fn field_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        field: &vir_mid::Field,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        match &*field.base {
            vir_mid::Expression::Local(local) if self.caller_kind.is_predicate_body() => {
                assert!(local.variable.is_self_variable());
                let field_place = lowerer.encode_field_place(
                    &local.variable.ty,
                    &field.field,
                    self.predicate_place(),
                    field.position,
                )?;
                let field_address = lowerer.encode_field_address(
                    &local.variable.ty,
                    &field.field,
                    self.predicate_address(),
                    field.position,
                )?;
                self.snap_call(
                    lowerer,
                    &field.field.ty,
                    field_place,
                    field_address,
                    local.position,
                )
            }
            vir_mid::Expression::Local(local) if self.caller_kind.is_assign_precondition() => {
                // FIXME: these assertions may be wrong.
                assert!(local.variable.is_self_variable());
                let CallerKind::AssignPrecondition { ref field_replacement_map, .. } = self.caller_kind else {
                    unreachable!()
                };
                assert!(field_replacement_map.contains_key(&field.field));
                Ok(field_replacement_map[&field.field].clone())
            }
            _ => self.field_to_snapshot_impl(lowerer, field, expect_math_bool),
        }
    }

    fn variable_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        assert!(
            !self.caller_kind.is_assign_precondition(),
            "all variables should be replaced by arguments; got: {variable}"
        );
        assert!(
            !self.caller_kind.is_predicate_body() || variable.is_self_variable(),
            "{variable} must be self"
        );
        if self.use_ssa && !self.bound_variable_stack.contains(variable) {
            if let Some(label) = &self.old_label {
                lowerer.snapshot_variable_version_at_label(variable, label)
            } else {
                lowerer.current_snapshot_variable_version(variable)
            }
        } else {
            Ok(vir_low::VariableDecl {
                name: variable.name.clone(),
                ty: self.type_to_snapshot(lowerer, &variable.ty)?,
            })
        }
    }

    fn labelled_old_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        old: &vir_mid::LabelledOld,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let parent_old_label = std::mem::replace(&mut self.old_label, Some(old.label.clone()));
        let result = self.expression_to_snapshot(lowerer, &old.base, expect_math_bool)?;
        self.old_label = parent_old_label;
        Ok(vir_low::Expression::labelled_old(
            Some(old.label.clone()),
            result,
            old.position,
        ))
    }

    fn func_app_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        app: &vir_mid::FuncApp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let arguments =
            self.expression_vec_to_snapshot(lowerer, &app.arguments, expect_math_bool)?;
        let return_type = self.type_to_snapshot(lowerer, &app.return_type)?;
        let func_app = lowerer.call_pure_function_in_procedure_context(
            app.get_identifier(),
            arguments,
            return_type,
            app.position,
        )?;
        let result = vir_low::Expression::FuncApp(func_app);
        self.ensure_bool_expression(lowerer, &app.return_type, result, expect_math_bool)
    }

    fn acc_predicate_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        acc_predicate: &vir_mid::AccPredicate,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(expect_math_bool);
        assert!(
            lowerer
                .check_mode
                .unwrap()
                .supports_accessibility_predicates_in_assertions()
                || matches!(self.caller_kind, CallerKind::PredicateBody { .. })
        );
        // assert_ne!(self.caller_kind, CallerKind::PlaceExpression, "unimplemented: report a proper error message");
        let expression = match &*acc_predicate.predicate {
            vir_mid::Predicate::OwnedNonAliased(predicate) => {
                let ty = predicate.place.get_type();
                let place = lowerer.encode_expression_as_place(&predicate.place)?;
                let address = self.pointer_deref_into_address(lowerer, &predicate.place)?;
                let acc = self.predicate(
                    lowerer,
                    ty,
                    place.clone(),
                    address.clone(),
                    predicate.position,
                )?;
                let snap_call =
                    self.snap_call(lowerer, ty, place, address, predicate.place.position())?;
                self.maybe_store_snap_call(lowerer, &predicate.place, &snap_call)?;
                self.snap_calls.push((predicate.place.clone(), snap_call));
                acc
            }
            vir_mid::Predicate::OwnedRange(predicate) => {
                let ty = predicate.address.get_type();
                let address = self.expression_to_snapshot(lowerer, &predicate.address, true)?;
                let start_index =
                    self.expression_to_snapshot(lowerer, &predicate.start_index, true)?;
                let end_index = self.expression_to_snapshot(lowerer, &predicate.end_index, true)?;
                self.range_snap_calls
                    .push((address.clone(), (ty.clone(), predicate.position)));
                self.maybe_store_range_snap_call(lowerer, &address, ty, predicate.position)?;
                let vir_mid::Type::Pointer(pointer_type) = ty else {
                    unreachable!();
                };
                self.created_predicate_types
                    .push((*pointer_type.target_type).clone());
                self.predicate_range(
                    lowerer,
                    ty,
                    address,
                    start_index,
                    end_index,
                    predicate.position,
                )?
                // lowerer.owned_aliased_range(
                //     self.call_context(),
                //     ty,
                //     ty,
                //     address,
                //     start_index,
                //     end_index,
                //     None,
                //     predicate.position,
                // )?
            }
            vir_mid::Predicate::MemoryBlockHeap(predicate) => {
                match self.predicate_kind {
                    PredicateKind::Owned => {
                        let address =
                            self.pointer_deref_into_address(lowerer, &predicate.address)?;
                        // let place = lowerer.encode_expression_as_place(&predicate.address)?;
                        // let address =
                        //     self.pointer_deref_into_address(lowerer, &predicate.address)?;
                        // use vir_low::macros::*;
                        // let compute_address = ty!(Address);
                        // let address = expr! {
                        //     ComputeAddress::compute_address([place], [address])
                        // };
                        let size = self.expression_to_snapshot(
                            lowerer,
                            &predicate.size,
                            expect_math_bool,
                        )?;
                        lowerer.encode_memory_block_acc(address, size, acc_predicate.position)?
                    }
                    PredicateKind::FracRef { .. } | PredicateKind::UniqueRef { .. } => {
                        // Memory blocks are not accessible in frac/unique ref predicates.
                        true.into()
                    }
                }
            }
            vir_mid::Predicate::MemoryBlockHeapDrop(predicate) => {
                match self.predicate_kind {
                    PredicateKind::Owned => {
                        // FIXME: Why this does not match the encoding of MemoryBlockHeap?
                        let address =
                            self.pointer_deref_into_address(lowerer, &predicate.address)?;
                        let size = self.expression_to_snapshot(
                            lowerer,
                            &predicate.size,
                            expect_math_bool,
                        )?;
                        lowerer.encode_memory_block_heap_drop_acc(
                            address,
                            size,
                            acc_predicate.position,
                        )?
                    }
                    PredicateKind::FracRef { .. } | PredicateKind::UniqueRef { .. } => {
                        // Memory blocks are not accessible in frac/unique ref predicates.
                        true.into()
                    }
                }
            }
            vir_mid::Predicate::MemoryBlockHeapRange(predicate) => {
                let pointer_value =
                    self.expression_to_snapshot(lowerer, &predicate.address, true)?;
                let address = lowerer.pointer_address(
                    predicate.address.get_type(),
                    pointer_value,
                    predicate.position,
                )?;
                let size = self.expression_to_snapshot(lowerer, &predicate.size, true)?;
                let start_index =
                    self.expression_to_snapshot(lowerer, &predicate.start_index, true)?;
                let end_index = self.expression_to_snapshot(lowerer, &predicate.end_index, true)?;
                lowerer.encode_memory_block_range_acc(
                    address,
                    size,
                    start_index,
                    end_index,
                    acc_predicate.position,
                )?
            }
            _ => unimplemented!("{acc_predicate}"),
        };
        if self.is_target_pure {
            Ok(true.into())
        } else {
            Ok(expression)
        }
    }

    fn deref_own(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        pointer_type: &vir_mid::Type,
        pointer: vir_low::Expression,
        index: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // FIXME: improve error reporting by showing which permission was used
        // by linking to predicate_position.
        let pointer = pointer.remove_unnecessary_old();
        let comparison_pointer = if let Some(old_label) = &self.old_label {
            pointer.clone().remove_old_label(old_label)
        } else {
            pointer.clone()
        };
        let Some((_, (_todo_remove_ty, _predicate_position))) = self.get_range_snap_calls(lowerer)?.iter().find(|(range_pointer, _)| {
            range_pointer == &comparison_pointer
        }) else {
            unimplemented!("Report a proper error message about not syntactically framed deref_own: {pointer}");
        };
        // let address = lowerer.pointer_address(
        //     pointer_type,
        //     pointer,
        //     position,
        // )?;
        let vir_mid::Type::Pointer(ty) = pointer_type else {
            unreachable!()
        };
        let size_type = lowerer.size_type_mid()?;
        let index_int = lowerer.obtain_constant_value(&size_type, index, position)?;
        let element_address =
            lowerer.encode_index_address(pointer_type, pointer, index_int, position)?;
        let result = lowerer.owned_aliased_snap(
            self.call_context(),
            &ty.target_type,
            &*ty.target_type,
            element_address,
            position,
        )?;
        Ok(result)
    }

    // FIXME: Code duplication.
    fn pointer_deref_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        deref: &vir_mid::Deref,
        _base_snapshot: vir_low::Expression,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let span = lowerer
            .encoder
            .error_manager()
            .position_manager()
            .get_span(deref.position.into())
            .cloned()
            .unwrap();
        Err(SpannedEncodingError::incorrect(
            "the place must be syntactically framed by permissions",
            span,
        ))
        // TODO: outdated code, delete. Return true for now because we expect
        // the result to not be used.
        // unimplemented!("pointer_deref_to_snapshot: {deref} {base_snapshot}");
        // Ok(true.into())
        // let heap = self
        //     .unsafe_cell_values
        //     .clone()
        //     .expect("This function should be reachable only when heap is Some");
        // lowerer.pointer_target_snapshot_in_heap(
        //     deref.base.get_type(),
        //     heap,
        //     base_snapshot,
        //     deref.position,
        // )
    }

    fn unfolding_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        unfolding: &vir_mid::Unfolding,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // FIXME: Replace all unfolding expressions with snap function calls.
        // Currently, we just ignore all unfolding expressions.
        self.expression_to_snapshot(lowerer, &unfolding.body, expect_math_bool)
    }

    fn eval_in_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        eval_in: &vir_mid::EvalIn,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if eval_in.context_kind == vir_mid::EvalInContextKind::SafeConstructor {
            let ty = eval_in.context.get_type();
            let type_decl = lowerer.encoder.get_type_decl_mid(ty)?;
            let place = &*eval_in.context;
            let _position = eval_in.position;
            let constructor_call = match &type_decl {
                vir_mid::TypeDecl::Reference(decl) => {
                    match decl.uniqueness {
                        vir_mid::ty::Uniqueness::Unique => {
                            // FIXME: This is currently not implemented since we
                            // just hope that the specification needs only the
                            // deref of the reference than the actual reference
                            // itself.
                            true.into()
                            // for (place, snap_call) in &self.snap_calls {
                            //     eprintln!("place: {}", place);
                            //     eprintln!("  {}", place.get_type());
                            // }
                            // let address_place = vir_mid::Expression::field(
                            //     place.clone(),
                            //     vir_mid::FieldDecl::new(
                            //         ADDRESS_FIELD_NAME,
                            //         0usize,
                            //         vir_mid::Type::Int(vir_mid::ty::Int::Usize),
                            //     ),
                            //     position,
                            // );
                            // let reference_type = ty.clone().unwrap_reference();
                            // let target_type = *reference_type.target_type;
                            // let Some((_, target_address_snapshot)) = self.snap_calls.iter().find(|(place, _)| {
                            //     place == &address_place
                            // }) else {
                            //     unreachable!("Failed to find the address place: {address_place}");
                            // };
                            // let pointer_type = &lowerer.reference_address_type(ty)?;
                            // let target_address = lowerer.pointer_address(
                            //     pointer_type,
                            //     target_address_snapshot.clone(),
                            //     position,
                            // )?;
                            // let lifetime = reference_type.lifetime;
                            // let deref_place = vir_mid::Expression::deref(
                            //     place.clone(),
                            //     target_type.clone(),
                            //     position,
                            // );
                            // let Some((_, current_snapshot)) = self.snap_calls.iter().find(|(place, _)| {
                            //     place == &deref_place
                            // }) else {
                            //     unreachable!("Failed to find the address place: {address_place}");
                            // };
                            // let target_place = lowerer.encode_expression_as_place(&deref_place)?;
                            // let lifetime = lowerer
                            //     .encode_lifetime_const_into_procedure_variable(&lifetime)?
                            //     .into();
                            // let TODO_target_slice_len = None;
                            // let final_snapshot = lowerer.unique_ref_snap(
                            //     self.call_context(),
                            //     ty,
                            //     ty,
                            //     target_place,
                            //     target_address.clone(),
                            //     lifetime,
                            //     TODO_target_slice_len,
                            //     true,
                            //     position,
                            // )?;
                            // // use vir_low::macros::*;
                            // // let pointer_type = &lowerer.reference_address_type(ty)?;
                            // // let size_of = lowerer
                            // //     .encode_type_size_expression2(ty, &type_decl)?;
                            // // let bytes = lowerer
                            // //     .encode_memory_block_bytes_expression(address.into(), size_of)?;
                            // // let from_bytes = self.type_to_snapshot(lowerer, pointer_type)?;
                            // // let pointer_snapshot = expr! {
                            // //     Snap<pointer_type>::from_bytes([bytes])
                            // // };
                            // // let target_address = lowerer.pointer_address(
                            // //     pointer_type,
                            // //     pointer_snapshot.clone(),
                            // //     position,
                            // // )?;
                            // lowerer.unique_reference_snapshot_constructor(
                            //     &target_type,
                            //     target_address.clone(),
                            //     current_snapshot.clone(),
                            //     final_snapshot,
                            //     eval_in.position,
                            // )?
                        }
                        vir_mid::ty::Uniqueness::Shared => todo!(),
                    }
                }
                vir_mid::TypeDecl::Struct(decl) => {
                    assert!(decl.structural_invariant.is_none(), "report a proper error message that structs with invariants cannot be automatically folded");
                    // TODO: construct_struct_snapshot
                    unimplemented!("{decl}");
                }
                _ => unimplemented!("{type_decl}"),
            };
            self.snap_calls.push((place.clone(), constructor_call));
            let result = self.expression_to_snapshot(lowerer, &eval_in.body, expect_math_bool)?;
            self.snap_calls.pop();
            return Ok(result);
        }
        let box vir_mid::Expression::AccPredicate(predicate) = &eval_in.context else {
            unimplemented!("A proper error message that this must be a predicate: {}", eval_in.context);
        };
        let result = match &*predicate.predicate {
            vir_mid::Predicate::OwnedNonAliased(predicate) => {
                let (predicate_place, old_label) =
                    if let vir_mid::Expression::LabelledOld(vir_mid::LabelledOld {
                        label,
                        base,
                        ..
                    }) = &predicate.place
                    {
                        assert!(matches!(
                            eval_in.context_kind,
                            vir_mid::EvalInContextKind::Old
                                | vir_mid::EvalInContextKind::OldOpenedRefPredicate
                        ));
                        (&**base, Some(label))
                    } else {
                        assert!(matches!(
                            eval_in.context_kind,
                            vir_mid::EvalInContextKind::Predicate
                                | vir_mid::EvalInContextKind::OpenedRefPredicate
                        ));
                        (&predicate.place, None)
                    };
                let ty = predicate.place.get_type();
                let place = lowerer.encode_expression_as_place(predicate_place)?;
                let address = if predicate_place.is_behind_pointer_dereference() {
                    assert!(old_label.is_none(), "unimplemented: {predicate}");
                    self.pointer_deref_into_address(lowerer, predicate_place)?
                } else {
                    lowerer.encode_expression_as_place_address(predicate_place)?
                };
                let mut predicate_kind =
                    if let Some((lifetime, uniqueness)) = predicate_place.get_dereference_kind() {
                        let lifetime = lowerer
                            .encode_lifetime_const_into_procedure_variable(lifetime)?
                            .into();
                        match uniqueness {
                            vir_mid::ty::Uniqueness::Unique => PredicateKind::UniqueRef {
                                lifetime,
                                is_final: false,
                            },
                            vir_mid::ty::Uniqueness::Shared => PredicateKind::FracRef { lifetime },
                        }
                    } else {
                        PredicateKind::Owned
                    };
                if matches!(
                    eval_in.context_kind,
                    vir_mid::EvalInContextKind::OpenedRefPredicate
                        | vir_mid::EvalInContextKind::OldOpenedRefPredicate
                ) {
                    predicate_kind = PredicateKind::Owned;
                }
                let mut snap_call = self.snap_call_with_predicate_kind(
                    lowerer,
                    ty,
                    predicate_kind,
                    place,
                    address,
                    predicate.place.position(),
                )?;
                if let Some(old_label) = old_label {
                    snap_call = vir_low::Expression::labelled_old(
                        Some(old_label.to_string()),
                        snap_call,
                        predicate.place.position(),
                    )
                }
                self.snap_calls.push((predicate.place.clone(), snap_call));
                let result =
                    self.expression_to_snapshot(lowerer, &eval_in.body, expect_math_bool)?;
                self.snap_calls.pop();
                result
            }
            vir_mid::Predicate::OwnedRange(predicate) => {
                let ty = predicate.address.get_type();
                let address = self.expression_to_snapshot(lowerer, &predicate.address, true)?;
                self.range_snap_calls
                    .push((address, (ty.clone(), predicate.position)));
                let result =
                    self.expression_to_snapshot(lowerer, &eval_in.body, expect_math_bool)?;
                self.range_snap_calls.pop();
                result
            }
            _ => unimplemented!(
                "A proper error message that this must be an owned predicate: {predicate}"
            ),
        };
        Ok(result)
    }

    fn call_context(&self) -> CallContext {
        match self.caller_kind {
            CallerKind::PredicateBody { .. } | CallerKind::AssignPrecondition { .. } => {
                CallContext::BuiltinMethod
            }
            CallerKind::InhaleExhale => CallContext::Procedure,
        }
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
        variables: &[vir_mid::VariableDecl],
    ) -> SpannedEncodingResult<()> {
        self.bound_variable_stack.push(variables);
        Ok(())
    }

    fn pop_bound_variables(&mut self) -> SpannedEncodingResult<()> {
        self.bound_variable_stack.pop();
        Ok(())
    }
}
